module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorRelativeBoundaryLifting
public import SerrePositivity.InfinityCategories.Core.TrivialFibrationEquivalence

/-! # 全射 Hom 準同型な dg 関手の nerve の自明 Kan fibration 性

概要：対象上全射で全 Hom が次数ごと全射な準同型の dg 関手は、nerve で同値を与える。
方針：正次元の相対境界充填と零次元の対象持ち上げを全境界の判定へ組み合わせる。
規約：全境界の持ち上げから実際の同値データを得る。使われ方：β3 の平坦分解の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

/-- 全射 Hom 準同型な対象上全射の dg 関手の nerve は自明 Kan fibration。 -/
lemma dgNerve_map_trivialKanFibration_of_surjective_quasiIso (F : DGFunctor A D E)
    (ho : Function.Surjective F.obj)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i))
    (hq : HomQuasiIso F) : TrivialKanFibration (dgNerve.map F) := by
  apply (trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro b c sq
  cases n with
  | zero =>
    obtain ⟨u, hu⟩ := dgFunctor_lift_vertex F ho (SSet.yonedaEquiv c)
    refine CommSq.HasLift.mk' {
      l := SSet.yonedaEquiv.symm u
      fac_left := SSet.boundary.hom_ext₀
      fac_right := ?_ }
    apply SSet.yonedaEquiv.injective
    simp only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
    exact hu
  | succ n =>
    have hb : b ≫ dgNerve.map F = (∂Δ[n + 1]).ι ≫
        SSet.yonedaEquiv.symm (SSet.yonedaEquiv c) := by
      simpa only [Equiv.symm_apply_apply] using sq.w
    obtain ⟨L, hL, hF⟩ := dgFunctor_relative_boundary_lift F hs hq b (SSet.yonedaEquiv c) hb
    exact CommSq.HasLift.mk' {
      l := L
      fac_left := hL
      fac_right := by simpa only [Equiv.symm_apply_apply] using hF }

/-- 上の条件を満たす dg 関手の nerve は ∞ 圏の同値。 -/
lemma dgNerve_map_isQCatEquivalence_of_surjective_quasiIso (F : DGFunctor A D E)
    (ho : Function.Surjective F.obj)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i))
    (hq : HomQuasiIso F) : IsQCatEquivalence (dgNerve.map F) := by
  let := dgNerve_map_trivialKanFibration_of_surjective_quasiIso F ho hs hq
  exact isQCatEquivalence_of_trivialKanFibration _

/-- 増大関手の nerve の明示的な逆写像と可逆二胞体。 -/
def dgNerveEquivalenceOfSurjectiveQuasiIso (F : DGFunctor A D E)
    (ho : Function.Surjective F.obj)
    (hs : ∀ x y (i : ℤ), Function.Surjective ((F.map x y).f i))
    (hq : HomQuasiIso F) : QCatEquivalence (dgNerve A D) (dgNerve A E) := by
  let := dgNerve_map_trivialKanFibration_of_surjective_quasiIso F ho hs hq
  exact qCatEquivalenceOfTrivialKanFibration (dgNerve.map F)

end SerrePositivity.InfinityCategories
