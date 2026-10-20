module
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementEquation
public import SerrePositivity.InfinityCategories.Derived.DGPartialSimplexHorn
public import SerrePositivity.InfinityCategories.Derived.DGLastHornKnownCutEquations
public import SerrePositivity.InfinityCategories.Derived.DGInitialRefinementAvoidingFaces

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {n : ℕ}
variable (σ : (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D) (q : D)
variable (s : ForgetEnrichment.of (Complex A) q ⟶
  ForgetEnrichment.of (Complex A) ((HornData.knownData σ).obj 0))

/-- 元の全既知データの同じ閉始点細分。 -/
def dgGeneralLastHornSourceRefinementData : SimplexData A D (n + 2) :=
  dgSimplexDataInitialRefinement A D (HornData.knownData σ) q s

/-- 元の既知集合の全方程式は、同じ全体細分データで保存される。 -/
lemma dgGeneralLastHornSourceRefinementData_equation (I : Finset (Fin (n + 3)))
    (hf : I ≠ Finset.univ) (hm : I ≠ Finset.univ.erase (Fin.last (n + 2))) :
    (dgGeneralLastHornSourceRefinementData σ q s).Equation I :=
  dgSimplexDataInitialRefinement_equation A D (HornData.knownData σ) q s I
    (dgGeneralLastHornKnown_equation σ I hf hm)

/-- 元の全指定面を同じ実閉射で始点細分した、全次元の実最後外ホーン。 -/
def dgGeneralLastHornSourceRefinement :
    (Λ[n + 2, Fin.last (n + 2)] : SSet.{max u v}) ⟶ dgNerve A D :=
  dgPartialSimplexHorn (dgGeneralLastHornSourceRefinementData σ q s) (Fin.last (n + 2))
    (dgGeneralLastHornSourceRefinementData_equation σ q s)

/-- 新ホーンの各指定面は、元の全体細分データの同じ引き戻しを回収する。 -/
lemma dgGeneralLastHornSourceRefinement_knownData_face (j : Fin (n + 3))
    (hj : j ≠ Fin.last (n + 2)) :
    (HornData.knownData (dgGeneralLastHornSourceRefinement σ q s)).pullback
        j.succAboveOrderEmb.toOrderHom =
      (dgGeneralLastHornSourceRefinementData σ q s).pullback j.succAboveOrderEmb.toOrderHom :=
  dgPartialSimplexHorn_knownData_face _ _ _ j hj

/-- 元の零面は、同じ実ホーン写像として厳密に保たれる。 -/
lemma dgGeneralLastHornSourceRefinement_preserves_face_zero :
    horn.ι (Fin.last (n + 2)) 0 (by simp) ≫ dgGeneralLastHornSourceRefinement σ q s =
      horn.ι (Fin.last (n + 2)) 0 (by simp) ≫ σ := by
  apply (SSet.yonedaEquiv (X := dgNerve A D)).injective
  apply Simplex.ext
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι]
  rw [← HornData.knownData_pullback_face _ 0 (by simp),
    dgGeneralLastHornSourceRefinement_knownData_face σ q s 0 (by simp)]
  exact (dgSimplexDataInitialRefinement_pullback_avoids_zero A D
    (HornData.knownData σ) q s (0 : Fin (n + 3)).succAboveOrderEmb.toOrderHom
    (0 : Fin (n + 3)).succAboveOrderEmb.injective
    (fun i => by change i.succ ≠ 0; exact Fin.succ_ne_zero i)).trans
      (HornData.knownData_pullback_face σ 0 (by simp))

end SerrePositivity.InfinityCategories
