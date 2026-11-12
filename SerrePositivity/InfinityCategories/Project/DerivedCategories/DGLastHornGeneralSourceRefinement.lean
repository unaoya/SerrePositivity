module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementEquation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPartialSimplexHorn
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGLastHornKnownCutEquations
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGInitialRefinementAvoidingFaces

/-! # 全次元の実最後外ホーンの閉始点細分

概要：既知の全体データを一つの実閉射で細分し、その同じ全指定面を実ホーンへ貼る。
方針：各既知集合の方程式の保存と、部分データからの一般ホーン構成を使う。
規約：未知の二方程式はまだ要求しない。使われ方：追加分母後の Q・A による実充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ).obj 0))

/-- 元の全既知データの同じ閉始点細分。 -/
def dgGeneralLastHornSourceRefinementData : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 2) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) q s

/-- 元の既知集合の全方程式は、同じ全体細分データで保存される。 -/
lemma dgGeneralLastHornSourceRefinementData_equation (I : Finset (Fin (n + 3)))
    (hf : I ≠ Finset.univ) (hm : I ≠ Finset.univ.erase (Fin.last (n + 2))) :
    (dgGeneralLastHornSourceRefinementData σ q s).Equation I :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_equation A D (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) q s I
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGeneralLastHornKnown_equation σ I hf hm)

/-- 元の全指定面を同じ実閉射で始点細分した、全次元の実最後外ホーン。 -/
def dgGeneralLastHornSourceRefinement :
    (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPartialSimplexHorn (dgGeneralLastHornSourceRefinementData σ q s) (Fin.last (n + 2))
    (dgGeneralLastHornSourceRefinementData_equation σ q s)

/-- 新ホーンの各指定面は、元の全体細分データの同じ引き戻しを回収する。 -/
lemma dgGeneralLastHornSourceRefinement_knownData_face (j : Fin (n + 3))
    (hj : j ≠ Fin.last (n + 2)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (dgGeneralLastHornSourceRefinement σ q s)).pullback
        j.succAboveOrderEmb.toOrderHom =
      (dgGeneralLastHornSourceRefinementData σ q s).pullback j.succAboveOrderEmb.toOrderHom :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPartialSimplexHorn_knownData_face _ _ _ j hj

/-- 元の零面は、同じ実ホーン写像として厳密に保たれる。 -/
lemma dgGeneralLastHornSourceRefinement_preserves_face_zero :
    horn.ι (Fin.last (n + 2)) 0 (by simp) ≫ dgGeneralLastHornSourceRefinement σ q s =
      horn.ι (Fin.last (n + 2)) 0 (by simp) ≫ σ := by
  apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face _ 0 (by simp),
    dgGeneralLastHornSourceRefinement_knownData_face σ q s 0 (by simp)]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSimplexDataInitialRefinement_pullback_avoids_zero A D
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData σ) q s (0 : Fin (n + 3)).succAboveOrderEmb.toOrderHom
    (0 : Fin (n + 3)).succAboveOrderEmb.injective
    (fun i => by change i.succ ≠ 0; exact Fin.succ_ne_zero i)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face σ 0 (by simp))

end SerrePositivity.InfinityCategories.Project.DerivedCategories
