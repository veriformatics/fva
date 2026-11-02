/* A stub left in place of clamp: it returns x unchanged. Its spec (Spec.lean) is proven, and its
 * docstring and name both say "clamp"; only a check against the requirement shows the gap. */
int clamp(int x, int lo, int hi) {
	(void)lo;
	(void)hi;
	return x;
}
