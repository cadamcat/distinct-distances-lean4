import DistinctDistances.TrackC.HyperplaneFactor

open scoped Topology

namespace DistinctDistances.TrackC

/-- A real degree-one polynomial is irreducible. -/
theorem real_linear_polynomial_irreducible (l : Poly 3) (hl : l.totalDegree = 1) : Irreducible l := by
  apply MvPolynomial.irreducible_of_totalDegree_eq_one hl
  intro a ha
  apply isUnit_iff_ne_zero.mpr
  intro hzero
  subst a
  have hz : l = 0 := by
    apply MvPolynomial.ext
    intro m
    simpa using ha m
  rw [hz, MvPolynomial.totalDegree_zero] at hl
  omega

/-- An irreducible polynomial divisible by a degree-one equation is linear. -/
theorem irreducible_degree_one_of_linear_dvd (f l : Poly 3) (hf : Irreducible f)
    (hl : l.totalDegree = 1) (hdiv : l ∣ f) : f.totalDegree = 1 := by
  obtain ⟨h, hfh⟩ := hdiv
  have hlu : ¬ IsUnit l := by
    intro hu
    have hz := (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hu).2
    omega
  have hhu : IsUnit h := (hf.isUnit_or_isUnit hfh).resolve_left hlu
  have hl0 : l ≠ 0 := by
    intro hz
    rw [hz, MvPolynomial.totalDegree_zero] at hl
    omega
  have hh0 : h ≠ 0 := by
    intro hz
    apply hf.ne_zero
    rw [hfh, hz, mul_zero]
  rw [hfh, MvPolynomial.totalDegree_mul_of_isDomain hl0 hh0, hl,
    (MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp hhu).2]

/-- The smooth local flatness argument excludes nonlinear irreducible surfaces. -/
theorem irreducible_flat_surface_linear (f : Poly 3) (hf : Irreducible f) (x : E 3)
    (hx : regularPoint f x) (hflat : ∀ᶠ y in 𝓝 x, regularPoint f y → flatPoint f y) :
    f.totalDegree = 1 := by
  obtain ⟨l, hl, hdiv⟩ := flat_surface_linear_factor f x hx hflat
  exact irreducible_degree_one_of_linear_dvd f l hf hl hdiv

/-- A regular zero of one factor has nonzero value on its cofactor. -/
theorem regular_product_cofactor_ne_zero (g h : Poly 3) (x : E 3)
    (hx : regularPoint (g*h) x) (hg : evalR g x = 0) : evalR h x ≠ 0 := by
  intro hh
  obtain ⟨i, hi⟩ := hx.2
  apply hi
  change MvPolynomial.eval x (MvPolynomial.pderiv i (g*h)) = 0
  change MvPolynomial.eval x g = 0 at hg
  change MvPolynomial.eval x h = 0 at hh
  simp [MvPolynomial.pderiv_mul, hg, hh]

/-- Nonlinear factors supporting a regular flat line cannot divide every flatness test,
the thin factor obstruction in CI:188–206. The tests are supplied by ci:flat.tests. -/
theorem nonlinear_factor_flat_test_not_divisible (f g h : Poly 3) (hfg : f = g*h)
    (hg : Irreducible g) (hdegree : 1 < g.totalDegree) (x : E 3)
    (hx : regularPoint f x) (hgx : evalR g x = 0) (T : Fin 9 → Poly 3)
    (hT : ∀ y : E 3, regularPoint f y → (flatPoint f y ↔ ∀ j, evalR (T j) y = 0)) :
    ∃ j : Fin 9, ¬ g ∣ T j := by
  classical
  by_contra! hdiv
  have hhx : evalR h x ≠ 0 :=
    regular_product_cofactor_ne_zero g h x (hfg ▸ hx) hgx
  have hhnear : ∀ᶠ y in 𝓝 x, evalR h y ≠ 0 :=
    (polynomial_contDiff 3 h 0).continuous.continuousAt.eventually_ne hhx
  have hflat : ∀ᶠ y in 𝓝 x, regularPoint f y → flatPoint f y := by
    filter_upwards [hhnear] with y hhy
    intro hy
    have hzero : evalR g y * evalR h y = 0 := by
      simpa [hfg, evalR] using hy.1
    have hgy : evalR g y = 0 := (mul_eq_zero.mp hzero).resolve_right hhy
    apply (hT y hy).mpr
    intro j
    obtain ⟨q, hq⟩ := hdiv j
    rw [hq]
    change MvPolynomial.eval y (g*q) = 0
    change MvPolynomial.eval y g = 0 at hgy
    rw [map_mul, hgy, zero_mul]
  obtain ⟨l, hl, hlf, hlx⟩ := flat_surface_linear_factor_through_point f x hx hflat
  have hlprime : Prime l := irreducible_iff_prime.mp (real_linear_polynomial_irreducible l hl)
  have hlg_or_hlh : l ∣ g ∨ l ∣ h := hlprime.dvd_mul.mp (hfg ▸ hlf)
  rcases hlg_or_hlh with hlg | hlh
  · have hglinear := irreducible_degree_one_of_linear_dvd g l hg hl hlg
    omega
  · obtain ⟨q, hq⟩ := hlh
    apply hhx
    rw [hq]
    change MvPolynomial.eval x (l*q) = 0
    change MvPolynomial.eval x l = 0 at hlx
    rw [map_mul, hlx, zero_mul]

end DistinctDistances.TrackC
