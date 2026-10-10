import DistinctDistances.TrackA.RegularSectionConstantSupport

namespace DistinctDistances.TrackA
noncomputable section
open scoped Classical

/-- Avoiding every irreducible member makes the linear equation a
nonzero divisor on the actual reduced union's coordinate ring. -/
theorem projective_family_cancel_polynomial {n : ℕ} (F : ProjectiveFamily.Family n)
    (hF : ∀ V ∈ F, V.IsIrreducible) (ℓ : Poly n) (hℓ : ∀ V ∈ F, ℓ ∉ V.ideal)
    (f : Poly n) (hf : ℓ*f ∈ (ProjectiveFamily.locus F).ideal) :
    f ∈ (ProjectiveFamily.locus F).ideal := by
  rw [← (ProjectiveFamily.locus F).vanishingIdeal_points]
  apply MvPolynomial.mem_vanishingIdeal_iff.mpr
  rintro x ⟨hx0, hxF⟩
  rw [ProjectiveFamily.points_locus] at hxF
  simp only [Set.mem_iUnion] at hxF
  obtain ⟨V, hV, hxV⟩ := hxF
  have hprod := projective_family_member_subvariety F V hV hf
  have hfV := ((hF V hV).mem_or_mem hprod).resolve_left (hℓ V hV)
  exact ((ProjectiveVariety.mem_points_mk_iff V x hx0).mp hxV) f hfV

/-- Local candidates for division by a nonzero divisor agree wherever
both denominators are nonzero. Denominators can vanish on components. -/
theorem local_linear_division_cross_eval {n : ℕ} (V : ProjectiveVariety n)
    (ℓ : Poly n) (hcancel : ∀ f : Poly n, ℓ*f ∈ V.ideal → f ∈ V.ideal)
    (s : NonzeroConePoint V → ℂ) (a b c d : Poly n)
    (ha : ∀ x, MvPolynomial.eval x.val b ≠ 0 →
      s x * MvPolynomial.eval x.val b = MvPolynomial.eval x.val ℓ * MvPolynomial.eval x.val a)
    (hc : ∀ x, MvPolynomial.eval x.val d ≠ 0 →
      s x * MvPolynomial.eval x.val d = MvPolynomial.eval x.val ℓ * MvPolynomial.eval x.val c)
    (x : NonzeroConePoint V) (hb : MvPolynomial.eval x.val b ≠ 0)
    (hd : MvPolynomial.eval x.val d ≠ 0) :
    MvPolynomial.eval x.val a * MvPolynomial.eval x.val d =
      MvPolynomial.eval x.val c * MvPolynomial.eval x.val b := by
  have hprod : ℓ * ((b*d)*(a*d-c*b)) ∈ V.ideal := by
    rw [← V.vanishingIdeal_points]
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro y ⟨hy0, hyV⟩
    let z : NonzeroConePoint V := ⟨y, hy0, (ProjectiveVariety.mem_points_mk_iff V y hy0).mp hyV⟩
    simp only [map_mul, map_sub, MvPolynomial.aeval_eq_eval]
    by_cases hyb : MvPolynomial.eval y b = 0
    · rw [hyb]; ring
    by_cases hyd : MvPolynomial.eval y d = 0
    · rw [hyd]; ring
    have hza := ha z hyb
    have hzc := hc z hyd
    change s z * MvPolynomial.eval y b = MvPolynomial.eval y ℓ * MvPolynomial.eval y a at hza
    change s z * MvPolynomial.eval y d = MvPolynomial.eval y ℓ * MvPolynomial.eval y c at hzc
    calc
      MvPolynomial.eval y ℓ * ((MvPolynomial.eval y b * MvPolynomial.eval y d) *
          (MvPolynomial.eval y a * MvPolynomial.eval y d - MvPolynomial.eval y c * MvPolynomial.eval y b)) =
        (MvPolynomial.eval y b * MvPolynomial.eval y d) *
          ((MvPolynomial.eval y ℓ * MvPolynomial.eval y a) * MvPolynomial.eval y d -
            (MvPolynomial.eval y ℓ * MvPolynomial.eval y c) * MvPolynomial.eval y b) := by ring
      _ = 0 := by rw [← hza, ← hzc]; ring
  have hrel := hcancel _ hprod
  have heval := x.property.2 _ hrel
  have hcross : MvPolynomial.eval x.val (a*d-c*b) = 0 := by
    have hzero : (MvPolynomial.eval x.val b * MvPolynomial.eval x.val d) *
        MvPolynomial.eval x.val (a*d-c*b) = 0 := by
      simpa only [map_mul, MvPolynomial.aeval_eq_eval] using heval
    exact (mul_eq_zero.mp hzero).resolve_left (mul_ne_zero hb hd)
  simpa only [map_sub, map_mul, sub_eq_zero] using hcross

/-- Compatible homogeneous local candidates glue into an actual regular
section whose multiplication by the linear equation is the given one. -/
theorem section_linear_division_of_local {n D : ℕ} (V : ProjectiveVariety n)
    (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hcancel : ∀ f : Poly n, ℓ*f ∈ V.ideal → f ∈ V.ideal)
    (s : regularSectionSpace V (D+1))
    (hlocal : ∀ x : NonzeroConePoint V, ∃ (q : ℕ) (a b : Poly n),
      a.IsHomogeneous (q+D) ∧ b.IsHomogeneous q ∧ MvPolynomial.eval x.val b ≠ 0 ∧
      ∀ y, MvPolynomial.eval y.val b ≠ 0 →
        s.val y * MvPolynomial.eval y.val b = MvPolynomial.eval y.val ℓ * MvPolynomial.eval y.val a) :
    ∃ t : regularSectionSpace V D, sectionMultiplyLinear V D ℓ hℓ t = s := by
  choose q a b ha hb hbx he using hlocal
  let tval : NonzeroConePoint V → ℂ := fun x => MvPolynomial.eval x.val (a x) / MvPolynomial.eval x.val (b x)
  have ht : IsRegularHomogeneousSection V D tval := by
    intro x
    refine ⟨q x, a x, b x, ha x, hb x, hbx x, ?_⟩
    intro y hy
    have hcross := local_linear_division_cross_eval V ℓ hcancel s.val
      (a y) (b y) (a x) (b x) (he y) (he x) y (hbx y) hy
    change (MvPolynomial.eval y.val (a y) / MvPolynomial.eval y.val (b y)) *
      MvPolynomial.eval y.val (b x) = MvPolynomial.eval y.val (a x)
    apply mul_right_cancel₀ (hbx y)
    calc
      ((MvPolynomial.eval y.val (a y) / MvPolynomial.eval y.val (b y)) *
          MvPolynomial.eval y.val (b x)) * MvPolynomial.eval y.val (b y) =
          MvPolynomial.eval y.val (a y) * MvPolynomial.eval y.val (b x) := by
        field_simp [hbx y]
      _ = _ := hcross
  refine ⟨⟨tval, ht⟩, ?_⟩
  apply Subtype.ext
  funext x
  change MvPolynomial.eval x.val ℓ * (MvPolynomial.eval x.val (a x) /
    MvPolynomial.eval x.val (b x)) = s.val x
  apply mul_right_cancel₀ (hbx x)
  calc
    (MvPolynomial.eval x.val ℓ * (MvPolynomial.eval x.val (a x) /
        MvPolynomial.eval x.val (b x))) * MvPolynomial.eval x.val (b x) =
        MvPolynomial.eval x.val ℓ * MvPolynomial.eval x.val (a x) := by
      field_simp [hbx x]
    _ = s.val x * MvPolynomial.eval x.val (b x) := (he x x (hbx x)).symm

/-- Saturated cut-ideal membership provides homogeneous local quotients
for a section whose restriction to the reduced cut is zero. -/
theorem section_kernel_local_linear_division {n D : ℕ} (V W : ProjectiveVariety n)
    (hWV : W.Subvariety V) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hclear : ∀ f ∈ W.ideal, ∀ i : Fin n, ∃ r : ℕ,
      MvPolynomial.X i ^ r * f ∈ V.ideal ⊔ Ideal.span {ℓ})
    (s : regularSectionSpace V (D+1))
    (hszero : sectionRestriction V W hWV (D+1) s = 0) :
    ∀ x : NonzeroConePoint V, ∃ (q : ℕ) (a b : Poly n),
      a.IsHomogeneous (q+D) ∧ b.IsHomogeneous q ∧ MvPolynomial.eval x.val b ≠ 0 ∧
      ∀ y, MvPolynomial.eval y.val b ≠ 0 →
        s.val y * MvPolynomial.eval y.val b = MvPolynomial.eval y.val ℓ * MvPolynomial.eval y.val a := by
  intro x
  have hs : IsRegularHomogeneousSection V (D+1) s.val := s.property
  obtain ⟨q, a, b, ha, hb, hbx, he⟩ := hs x
  have hba : b*a ∈ W.ideal := by
    rw [← W.vanishingIdeal_points]
    apply MvPolynomial.mem_vanishingIdeal_iff.mpr
    rintro y ⟨hy0, hyW⟩
    let z : NonzeroConePoint W := ⟨y, hy0, (ProjectiveVariety.mem_points_mk_iff W y hy0).mp hyW⟩
    let zV := nonzeroConeInclusion V W hWV z
    by_cases hyb : MvPolynomial.eval y b = 0
    · simp only [map_mul, MvPolynomial.aeval_eq_eval, hyb, zero_mul]
    have hz := congrFun (congrArg Subtype.val hszero) z
    change s.val zV = 0 at hz
    have ha0 := he zV hyb
    change s.val zV * MvPolynomial.eval y b = MvPolynomial.eval y a at ha0
    rw [hz, zero_mul] at ha0
    simp only [map_mul, MvPolynomial.aeval_eq_eval, ← ha0, mul_zero]
  have hi : ∃ i, x.val i ≠ 0 := by
    by_contra h
    push Not at h
    exact x.property.1 (funext h)
  obtain ⟨i, hi⟩ := hi
  obtain ⟨r, hr⟩ := hclear (b*a) hba i
  let A : Poly n := MvPolynomial.X i ^ r * (b*a)
  have hA : A.IsHomogeneous (1+(r+q+q+D)) := by
    convert ((MvPolynomial.isHomogeneous_X ℂ i).pow r).mul (hb.mul ha) using 1 <;> omega
  have hr' : A ∈ Ideal.span {ℓ} ⊔ V.ideal := by simpa only [A, sup_comm] using hr
  obtain ⟨c, u, hu, hcu⟩ := Ideal.mem_span_singleton_sup.mp hr'
  have hrel : (1 : Poly n)*A-c*ℓ ∈ V.ideal := by
    have hEq : (1 : Poly n)*A-c*ℓ = u := by rw [← hcu]; ring
    rwa [hEq]
  obtain ⟨g, hg, hAg⟩ := homogeneous_fraction_division V A ℓ 1 c hA hℓ
    (MvPolynomial.isHomogeneous_one (Fin n) ℂ) hrel
  have hAg' : A-g*ℓ ∈ V.ideal := by simpa only [one_mul] using hAg
  let e : Poly n := MvPolynomial.X i ^ r * (b*b)
  have hehom : e.IsHomogeneous (r+q+q) := by
    convert ((MvPolynomial.isHomogeneous_X ℂ i).pow r).mul (hb.mul hb) using 1 <;> omega
  have hex : MvPolynomial.eval x.val e ≠ 0 := by
    dsimp [e]
    rw [map_mul, map_pow, map_mul, MvPolynomial.eval_X]
    exact mul_ne_zero (pow_ne_zero r hi) (mul_ne_zero hbx hbx)
  refine ⟨r+q+q, g, e, by simpa only [Nat.zero_add] using hg, hehom, hex, ?_⟩
  intro y hey
  have hyb : MvPolynomial.eval y.val b ≠ 0 := by
    intro hyb
    apply hey
    simp only [e, map_mul, hyb, mul_zero]
  have hidentity : MvPolynomial.eval y.val A =
      MvPolynomial.eval y.val g * MvPolynomial.eval y.val ℓ := by
    have hz := y.property.2 (A-g*ℓ) hAg'
    simpa only [map_sub, map_mul, MvPolynomial.aeval_eq_eval, sub_eq_zero] using hz
  calc
    s.val y * MvPolynomial.eval y.val e =
        (MvPolynomial.eval y.val (MvPolynomial.X i ^ r) * MvPolynomial.eval y.val b) *
          (s.val y * MvPolynomial.eval y.val b) := by
      simp only [e, map_mul]
      ring
    _ = (MvPolynomial.eval y.val (MvPolynomial.X i ^ r) * MvPolynomial.eval y.val b) *
        MvPolynomial.eval y.val a := by rw [he y hyb]
    _ = MvPolynomial.eval y.val A := by
      simp only [A, map_mul]
      ring
    _ = MvPolynomial.eval y.val ℓ * MvPolynomial.eval y.val g := by rw [hidentity]; ring

/-- The actual section restriction sequence is exact whenever the cut
ideal is the coordinate-power saturation of the linear equation and the
equation is a nonzero divisor. No section-rank recurrence is assumed. -/
theorem sectionRestriction_ker_eq_range_of_power_clear {n : ℕ} (V W : ProjectiveVariety n)
    (hWV : W.Subvariety V) (D : ℕ) (ℓ : Poly n) (hℓ : ℓ.IsHomogeneous 1)
    (hcancel : ∀ f : Poly n, ℓ*f ∈ V.ideal → f ∈ V.ideal)
    (hclear : ∀ f ∈ W.ideal, ∀ i : Fin n, ∃ r : ℕ,
      MvPolynomial.X i ^ r * f ∈ V.ideal ⊔ Ideal.span {ℓ})
    (hℓW : ℓ ∈ W.ideal) :
    LinearMap.ker (sectionRestriction V W hWV (D+1)) =
      LinearMap.range (sectionMultiplyLinear V D ℓ hℓ) := by
  ext s
  constructor
  · intro hs
    obtain ⟨t, ht⟩ := section_linear_division_of_local V ℓ hℓ hcancel s
      (section_kernel_local_linear_division V W hWV ℓ hℓ hclear s (LinearMap.mem_ker.mp hs))
    exact ⟨t, ht⟩
  · rintro ⟨t, rfl⟩
    apply LinearMap.mem_ker.mpr
    apply Subtype.ext
    funext x
    change MvPolynomial.eval x.val ℓ * t.val (nonzeroConeInclusion V W hWV x) = 0
    have hzero : MvPolynomial.eval x.val ℓ = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval] using x.property.2 ℓ hℓW
    rw [hzero, zero_mul]

end
end DistinctDistances.TrackA
