use std::{
    cmp,
    collections::{BTreeSet, HashMap},
};

use super::RegionShape;
use crate::{
    circuit::RegionStart,
    plonk::{Any, Column},
};

/// A region allocated within a column.
#[derive(Clone, Default, Debug, PartialEq, Eq)]
struct AllocatedRegion {
    // The starting position of the region.
    start: usize,
    // The length of the region.
    length: usize,
}

impl Ord for AllocatedRegion {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        self.start.cmp(&other.start)
    }
}

impl PartialOrd for AllocatedRegion {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// An area of empty space within a column.
struct EmptySpace {
    // The starting position of the empty space.
    start: usize,
    // The number of rows of empty space, or `None` if unbounded.
    end: Option<usize>,
}

/// Allocated rows within a column.
///
/// This is a set of [a_start, a_end) pairs representing disjoint allocated intervals.
#[derive(Clone, Default, Debug)]
struct Allocations(BTreeSet<AllocatedRegion>);

impl Allocations {
    /// Return all the *unallocated* nonempty intervals intersecting [start, end).
    ///
    /// `end = None` represents an unbounded end.
    fn free_intervals(
        &self,
        start: usize,
        end: Option<usize>,
    ) -> impl Iterator<Item = EmptySpace> + '_ {
        self.0
            .iter()
            .map(Some)
            .chain(Some(None))
            .scan(start, move |row, region| {
                Some(if let Some(region) = region {
                    if end.map(|end| region.start >= end).unwrap_or(false) {
                        None
                    } else {
                        let ret = if *row < region.start {
                            Some(EmptySpace {
                                start: *row,
                                end: Some(region.start),
                            })
                        } else {
                            None
                        };

                        *row = cmp::max(*row, region.start + region.length);

                        ret
                    }
                } else if end.map(|end| *row < end).unwrap_or(true) {
                    Some(EmptySpace { start: *row, end })
                } else {
                    None
                })
            })
            .flatten()
    }
}

/// - `start` is the current start row of the region (not of this column).
/// - `slack` is the maximum number of rows the start could be moved down, taking into
///   account prior columns.
fn first_fit_region(
    column_allocations: &mut HashMap<Column<Any>, Allocations>,
    region_columns: &[Column<Any>],
    region_length: usize,
    start: usize,
    slack: Option<usize>,
) -> Option<usize> {
    let (c, remaining_columns) = match region_columns.split_first() {
        Some(cols) => cols,
        None => return Some(start),
    };
    let end = slack.map(|slack| start + region_length + slack);

    // Iterate over the unallocated non-empty intervals in c that intersect [start, end).
    for space in column_allocations
        .entry(*c)
        .or_default()
        .clone()
        .free_intervals(start, end)
    {
        // Do we have enough room for this column of the region in this interval?
        let s_slack = space
            .end
            .map(|end| (end as isize - space.start as isize) - region_length as isize);
        if let Some((slack, s_slack)) = slack.zip(s_slack) {
            assert!(s_slack <= slack as isize);
        }
        if s_slack.unwrap_or(0) >= 0 {
            let row = first_fit_region(
                column_allocations,
                remaining_columns,
                region_length,
                space.start,
                s_slack.map(|s| s as usize),
            );
            if let Some(row) = row {
                if let Some(end) = end {
                    assert!(row + region_length <= end);
                }
                column_allocations
                    .get_mut(c)
                    .unwrap()
                    .0
                    .insert(AllocatedRegion {
                        start: row,
                        length: region_length,
                    });
                return Some(row);
            }
        }
    }

    // No placement worked; the caller will need to try other possibilities.
    None
}

/// Positions the regions starting at the earliest row for which none of the columns are
/// in use, taking into account gaps between earlier regions.
fn slot_in(region_shapes: Vec<RegionShape>) -> Vec<(RegionStart, RegionShape)> {
    // Tracks the empty regions for each column.
    let mut column_allocations: HashMap<Column<Any>, Allocations> = Default::default();

    region_shapes
        .into_iter()
        .map(|region| {
            // Sort the region's columns to ensure determinism.
            // - An unstable sort is fine, because region.columns() returns a set.
            // - The sort order relies on Column's Ord implementation!
            let mut region_columns: Vec<_> = region.columns().iter().cloned().collect();
            region_columns.sort_unstable();

            let region_start = first_fit_region(
                &mut column_allocations,
                &region_columns,
                region.row_count(),
                0,
                None,
            )
            .expect("We can always fit a region somewhere");

            (region_start.into(), region)
        })
        .collect()
}

/// Sorts the regions by advice area and then lays them out with the [`slot_in`] strategy.
pub fn slot_in_biggest_advice_first(region_shapes: Vec<RegionShape>) -> Vec<RegionStart> {
    let mut sorted_regions: Vec<_> = region_shapes.into_iter().collect();
    sorted_regions.sort_unstable_by_key(|shape| {
        // Count the number of advice columns
        let advice_cols = shape
            .columns()
            .iter()
            .filter(|c| matches!(c.column_type(), Any::Advice))
            .count();
        // Sort by advice area (since this has the most contention).
        advice_cols * shape.row_count()
    });
    sorted_regions.reverse();

    // Lay out the sorted regions.
    let mut regions = slot_in(sorted_regions);

    // Un-sort the regions so they match the original indexing.
    regions.sort_unstable_by_key(|(_, region)| region.region_index().0);
    regions.into_iter().map(|(start, _)| start).collect()
}

#[test]
fn test_slot_in() {
    let regions = vec![
        RegionShape {
            region_index: 0.into(),
            columns: vec![Column::new(0, Any::Advice), Column::new(1, Any::Advice)]
                .into_iter()
                .collect(),
            row_count: 15,
        },
        RegionShape {
            region_index: 1.into(),
            columns: vec![Column::new(2, Any::Advice)].into_iter().collect(),
            row_count: 10,
        },
        RegionShape {
            region_index: 2.into(),
            columns: vec![Column::new(2, Any::Advice), Column::new(0, Any::Advice)]
                .into_iter()
                .collect(),
            row_count: 10,
        },
    ];
    assert_eq!(
        slot_in(regions)
            .into_iter()
            .map(|(i, _)| i)
            .collect::<Vec<_>>(),
        vec![0.into(), 0.into(), 15.into()]
    );
}