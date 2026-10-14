module

public import SerrePositivity.CommutativeAlgebra.PerfectoidRootTorsion
public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealPowers
public import SerrePositivity.CommutativeAlgebra.AdicKernelQuotient

/-! # pねじれを除く商とperfectoidイデアルの比較

pねじれのイデアルを実際に定義し、その商の完備性・pの非零因子性を証明する。
商のperfectoid性はFontaine核の単項性の確認へ還元し、普遍性による比較の境界を保つ。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity

/-- pで消える元のイデアル。 -/
def pTorsionIdeal (S : Type u) [CommRing S] (p : ℕ) : Ideal S where
  carrier := {x | (p : S) * x = 0}
  zero_mem' := mul_zero _
  add_mem' := by
    intro a b ha hb
    change (p : S) * a = 0 at ha
    change (p : S) * b = 0 at hb
    change (p : S) * (a + b) = 0
    rw [mul_add, ha, hb, add_zero]
  smul_mem' := by
    intro a b hb
    change (p : S) * b = 0 at hb
    change (p : S) * (a * b) = 0
    rw [mul_left_comm, hb, mul_zero]

@[simp] theorem mem_pTorsionIdeal (S : Type u) [CommRing S] (p : ℕ) (x : S) :
    x ∈ pTorsionIdeal S p ↔ (p : S) * x = 0 := Iff.rfl

/-- p進完備な環のpねじれ商はp進完備。perfectoid性やNoether性は不要。 -/
theorem pTorsionQuotient_isAdicComplete
    (S : Type u) [CommRing S] (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : S)}) S] :
    IsAdicComplete (Ideal.span {(p : S ⧸ pTorsionIdeal S p)})
      (S ⧸ pTorsionIdeal S p) := by
  have hker : pTorsionIdeal S p = LinearMap.ker (LinearMap.mulLeft S (p : S)) := rfl
  let : IsAdicComplete (Ideal.span {(p : S)}) (S ⧸ pTorsionIdeal S p) := by
    rw [hker]
    exact isAdicComplete_quotient_ker (Ideal.span {(p : S)})
      (LinearMap.mulLeft S (p : S))
  have hmap : (Ideal.span {(p : S)}).map
      (algebraMap S (S ⧸ pTorsionIdeal S p)) =
      Ideal.span {(p : S ⧸ pTorsionIdeal S p)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap]
  exact (IsAdicComplete.map_algebraMap_iff _ _).mpr inferInstance

/-- perfectoid環のpねじれ商の完備性。零環の場合も含む。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_isAdicComplete
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    IsAdicComplete (Ideal.span {(p : S ⧸ pTorsionIdeal S p)})
      (S ⧸ pTorsionIdeal S p) := by
  rcases hS with hsub | ⟨_, hc, _⟩
  · let : Subsingleton S := hsub
    infer_instance
  · let := hc
    exact SerrePositivity.pTorsionQuotient_isAdicComplete S p

/-- 単元倍のp乗根という関係式は商へ移る。 -/
theorem IsIntegralPerfectoid.exists_unit_p_root_quotient
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (I : Ideal S) : ∃ (π : S ⧸ I) (u : (S ⧸ I)ˣ), (p : S ⧸ I) = u * π ^ p := by
  rcases hS with hsub | ⟨_, _, ⟨π, u, hπ⟩, _⟩
  · let : Subsingleton S := hsub
    exact ⟨0, 1, Subsingleton.elim _ _⟩
  · let q := Ideal.Quotient.mk I
    refine ⟨q π, Units.map q.toMonoidHom u, ?_⟩
    change (p : S ⧸ I) = q (u : S) * (q π) ^ p
    simpa only [map_mul, map_pow, map_natCast] using congrArg q hπ

/-- perfectoid環のpねじれを除いた商では、pは非零因子として作用する。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_p_mul_injective
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p) :
    Function.Injective (fun x : S ⧸ pTorsionIdeal S p ↦ (p : S ⧸ pTorsionIdeal S p) * x) := by
  have hzero (x : S ⧸ pTorsionIdeal S p) (hx : (p : S ⧸ pTorsionIdeal S p) * x = 0) :
      x = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hx' : (p : S) * ((p : S) * x) = 0 := by
      apply (mem_pTorsionIdeal S p _).mp
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_mul, map_natCast]
      exact hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact hS.p_mul_eq_zero_of_pow_mul_eq_zero S p 2 x
      (by simpa only [pow_two, mul_assoc] using hx')
  intro x y hxy
  dsimp only at hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [mul_sub, hxy, sub_self]

/-- pねじれ商では、p=unit·π^Nの任意の正冪根も非零因子。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_root_mul_injective
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (π : S ⧸ pTorsionIdeal S p) (u : (S ⧸ pTorsionIdeal S p)ˣ)
    (N : ℕ) (hN : 0 < N) (hπ : (p : S ⧸ pTorsionIdeal S p) = u * π ^ N) :
    Function.Injective (fun x : S ⧸ pTorsionIdeal S p ↦ π * x) := by
  intro x y hxy
  change π * x = π * y at hxy
  apply hS.pTorsionQuotient_p_mul_injective S p
  dsimp only
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  simp only [hπ, pow_succ, mul_assoc, hxy]

/-- 任意の商でもmod pのFrobeniusの全射性は引き継がれる。完備性やFontaine核は別途必要。 -/
theorem IsIntegralPerfectoid.surjective_pow_mod_p_quotient
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (I : Ideal S) :
    Function.Surjective (fun x : (S ⧸ I) ⧸ Ideal.span {(p : S ⧸ I)} ↦ x ^ p) := by
  rcases hS with hsub | ⟨_, _, _, hF, _⟩
  · let : Subsingleton S := hsub
    intro x
    exact ⟨0, Subsingleton.elim _ _⟩
  · let q := Ideal.Quotient.mk I
    have hmap : Ideal.span {(p : S)} ≤ (Ideal.span {(p : S ⧸ I)}).comap q := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
      exact Ideal.subset_span (Set.mem_singleton _)
    let f := Ideal.quotientMap (Ideal.span {(p : S ⧸ I)}) q hmap
    have hf : Function.Surjective f := Ideal.quotientMap_surjective Ideal.Quotient.mk_surjective
    intro x
    obtain ⟨y, hy⟩ := hf x
    obtain ⟨z, hz⟩ := hF y
    refine ⟨f z, ?_⟩
    change (f z) ^ p = x
    change z ^ p = y at hz
    rw [← map_pow, hz, hy]

/-- pねじれ商のperfectoid性の確認をFontaine核の単項性だけに還元する。
完備性・p乗根・mod p Frobeniusの全射性は元の四条件から供給する。 -/
theorem IsIntegralPerfectoid.pTorsionQuotient_perfectoid_of_fontaine_kernel
    (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime] (hS : IsIntegralPerfectoid S p)
    (hker : ∀ (hp : ¬ IsUnit (p : S ⧸ pTorsionIdeal S p))
      (hc : IsAdicComplete (Ideal.span {(p : S ⧸ pTorsionIdeal S p)})
        (S ⧸ pTorsionIdeal S p)),
      letI : Fact (¬ IsUnit (p : S ⧸ pTorsionIdeal S p)) := ⟨hp⟩
      letI := hc
      (RingHom.ker (WittVector.fontaineTheta (S ⧸ pTorsionIdeal S p) p)).IsPrincipal) :
    IsIntegralPerfectoid (S ⧸ pTorsionIdeal S p) p := by
  let Q := S ⧸ pTorsionIdeal S p
  let hc : IsAdicComplete (Ideal.span {(p : Q)}) Q :=
    hS.pTorsionQuotient_isAdicComplete S p
  by_cases hsub : Subsingleton Q
  · exact Or.inl hsub
  · have hp : ¬ IsUnit (p : Q) := by
      intro hu
      have ht : Ideal.span {(p : Q)} = ⊤ := Ideal.span_singleton_eq_top.mpr hu
      have hh : IsHausdorff (⊤ : Ideal Q) Q := ht ▸ hc.toIsHausdorff
      exact hsub hh.subsingleton
    exact Or.inr ⟨hp, hc, hS.exists_unit_p_root_quotient S p _,
      hS.surjective_pow_mod_p_quotient S p _, hker hp hc⟩

/-- perfectoidなpねじれ商があれば、p^c g'で消える射からg'のperfectoidイデアルの像はpねじれ。
商のperfectoid性を単にpの非零因子性から推論しない。 -/
theorem perfectoidIdeal_image_p_mul_eq_zero_of_torsionQuotient_perfectoid
    (R S : Type u) [CommRing R] [CommRing S] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (hS : IsIntegralPerfectoid S p)
    (hQ : IsIntegralPerfectoid (S ⧸ pTorsionIdeal S p) p)
    (f : R →+* S) (g' : R) (c : ℕ) (hg : (p : S) ^ c * f g' = 0)
    (x : R) (hx : x ∈ perfectoidIdeal R p hR g') : (p : S) * f x = 0 := by
  let : Algebra.FinitePresentation R (R ⧸ Ideal.span {g'}) :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span_singleton g')
  let q := Ideal.Quotient.mk (pTorsionIdeal S p)
  have hfg : g' ∈ RingHom.ker (q.comp f) := by
    change q (f g') = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (hS.p_mul_eq_zero_of_pow_mul_eq_zero S p c (f g') hg)
  let k : R ⧸ Ideal.span {g'} →+* S ⧸ pTorsionIdeal S p :=
    Ideal.Quotient.lift _ (q.comp f) ((Ideal.span_singleton_le_iff_mem _).mpr hfg)
  let hu := isPerfectoidization_toPerfectoidization R (R ⧸ Ideal.span {g'}) p hR
  have he := RingHom.congr_fun (IsPerfectoidization.lift_comp hu hQ k)
    (Ideal.Quotient.mk (Ideal.span {g'}) x)
  change toPerfectoidization R (R ⧸ Ideal.span {g'}) p hR
    (Ideal.Quotient.mk (Ideal.span {g'}) x) = 0 at hx
  rw [RingHom.comp_apply, hx, map_zero] at he
  exact Ideal.Quotient.eq_zero_iff_mem.mp he.symm

end SerrePositivity
