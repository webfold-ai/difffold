//! Myers O(ND) line diff in linear space (middle snake, divide and conquer).
//!
//! Input is two sequences of interned line ids. Output is a delete flag per `a` line and an insert
//! flag per `b` line; everything unflagged is a match, in order. A work budget bounds the cost on
//! pathological inputs; when it runs out the remaining subproblem is emitted as delete-all plus
//! insert-all, which is still a valid (just larger) edit script. `capped` reports that.

/// Result of [`diff`].
#[derive(Debug, Clone)]
pub struct Myers {
	pub del: Vec<bool>,
	pub ins: Vec<bool>,
	/// True when the work budget ran out and part of the script is a plain replace.
	pub capped: bool,
}

/// Default work budget in inner-loop steps.
pub const DEFAULT_BUDGET: u64 = 400_000_000;

struct Ctx<'a> {
	a: &'a [u32],
	b: &'a [u32],
	del: Vec<bool>,
	ins: Vec<bool>,
	vf: Vec<isize>,
	vb: Vec<isize>,
	budget: u64,
	capped: bool,
}

/// Diff with the default budget.
#[must_use]
pub fn diff(a: &[u32], b: &[u32]) -> Myers {
	diff_with_budget(a, b, DEFAULT_BUDGET)
}

/// Diff with an explicit budget.
#[must_use]
pub fn diff_with_budget(a: &[u32], b: &[u32], budget: u64) -> Myers {
	let mut c = Ctx { a, b, del: vec![false; a.len()], ins: vec![false; b.len()], vf: Vec::new(), vb: Vec::new(), budget, capped: false };
	let max = (a.len() + b.len()).div_ceil(2) + 2;
	c.vf = vec![0; 2 * max + 6];
	c.vb = vec![0; 2 * max + 6];
	c.rec(0, a.len(), 0, b.len());
	Myers { del: c.del, ins: c.ins, capped: c.capped }
}

impl Ctx<'_> {
	fn replace(&mut self, alo: usize, ahi: usize, blo: usize, bhi: usize) {
		self.del[alo..ahi].iter_mut().for_each(|x| *x = true);
		self.ins[blo..bhi].iter_mut().for_each(|x| *x = true);
	}

	fn rec(&mut self, mut alo: usize, mut ahi: usize, mut blo: usize, mut bhi: usize) {
		while alo < ahi && blo < bhi && self.a[alo] == self.b[blo] {
			alo += 1;
			blo += 1;
		}
		while alo < ahi && blo < bhi && self.a[ahi - 1] == self.b[bhi - 1] {
			ahi -= 1;
			bhi -= 1;
		}
		if alo == ahi || blo == bhi {
			self.replace(alo, ahi, blo, bhi);
			return;
		}
		let a = &self.a[alo..ahi];
		let b = &self.b[blo..bhi];
		let Some((xs, ys, xe, ye)) = middle_snake(a, b, &mut self.vf, &mut self.vb, &mut self.budget) else {
			self.capped = true;
			self.replace(alo, ahi, blo, bhi);
			return;
		};
		let (n, m) = (a.len(), b.len());
		if xs == 0 && ys == 0 && xe == n && ye == m {
			// No progress is impossible for a correct split; fail safe rather than loop.
			self.capped = true;
			self.replace(alo, ahi, blo, bhi);
			return;
		}
		self.rec(alo, alo + xs, blo, blo + ys);
		self.rec(alo + xe, ahi, blo + ye, bhi);
	}
}

/// Returns the middle snake as `(x_start, y_start, x_end, y_end)` in `a`/`b` coordinates, or `None`
/// when the budget is exhausted. The two sides outside the snake are diffed recursively.
fn middle_snake(a: &[u32], b: &[u32], vf: &mut [isize], vb: &mut [isize], budget: &mut u64) -> Option<(usize, usize, usize, usize)> {
	let n = a.len() as isize;
	let m = b.len() as isize;
	let delta = n - m;
	let odd = delta & 1 != 0;
	let max = (n + m + 1) / 2;
	let off = max + 2;
	vf[(off + 1) as usize] = 0;
	vb[(off + 1) as usize] = 0;
	for d in 0..=max {
		let mut k = -d;
		while k <= d {
			if *budget == 0 {
				return None;
			}
			*budget -= 1;
			let ki = (off + k) as usize;
			let mut x = if k == -d || (k != d && vf[ki - 1] < vf[ki + 1]) { vf[ki + 1] } else { vf[ki - 1] + 1 };
			let mut y = x - k;
			let (x0, y0) = (x, y);
			while x < n && y < m && a[x as usize] == b[y as usize] {
				x += 1;
				y += 1;
				*budget = budget.saturating_sub(1);
			}
			vf[ki] = x;
			if odd {
				let kr = delta - k;
				if kr >= -(d - 1) && kr <= d - 1 && x + vb[(off + kr) as usize] >= n {
					return Some((x0 as usize, y0 as usize, x as usize, y as usize));
				}
			}
			k += 2;
		}
		let mut k = -d;
		while k <= d {
			if *budget == 0 {
				return None;
			}
			*budget -= 1;
			let ki = (off + k) as usize;
			let mut x = if k == -d || (k != d && vb[ki - 1] < vb[ki + 1]) { vb[ki + 1] } else { vb[ki - 1] + 1 };
			let mut y = x - k;
			let (x0, y0) = (x, y);
			while x < n && y < m && a[(n - 1 - x) as usize] == b[(m - 1 - y) as usize] {
				x += 1;
				y += 1;
				*budget = budget.saturating_sub(1);
			}
			vb[ki] = x;
			if !odd {
				let kr = delta - k;
				if kr >= -d && kr <= d && x + vf[(off + kr) as usize] >= n {
					return Some(((n - x) as usize, (m - y) as usize, (n - x0) as usize, (m - y0) as usize));
				}
			}
			k += 2;
		}
	}
	None
}

/// Number of deleted plus inserted lines.
#[must_use]
pub fn edit_distance(r: &Myers) -> usize {
	r.del.iter().filter(|x| **x).count() + r.ins.iter().filter(|x| **x).count()
}
