module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.EquationTransfer
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-! # 既知方程式を持つ単体データからの実ホーン

概要：未知の二集合以外で方程式を満たす全体データの各面を、実ホーンへ貼り合わせる。
方針：単射面の像の方程式を読み、同じデータの二重引き戻しの一致を使う。
規約：未知方程式や充填を仮定しない。使われ方：全次数の閉始点細分ホーン。
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
variable (t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 2)) (i : Fin (n + 3))
variable (ht : ∀ I, I ≠ Finset.univ → I ≠ Finset.univ.erase i → t.Equation I)

/-- 同じ全体データの利用可能な各面は、実際の dg 単体となる。 -/
def dgPartialSimplexHornFace (j : Fin (n + 3)) (hj : j ≠ i) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D (n + 1) where
  toSimplexData := t.pullback j.succAboveOrderEmb.toOrderHom
  equation J a b k hJ ha hb hk := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_hom_of_inj _ _ _ _ _ _ _ _ _ _
      j.succAboveOrderEmb.injective.injOn,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.pullback_rhs_of_inj _ _ _ _ _ _ _ _ _ _
        j.succAboveOrderEmb.injective.injOn]
    exact ht _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.image_known j hj J).1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.image_known j hj J).2 _ _ _ _ _ _ _

/-- 各実面の米田表示。 -/
def dgPartialSimplexHornFaceMap (j : Fin (n + 3)) (hj : j ≠ i) : Δ[n + 1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).symm (dgPartialSimplexHornFace t i ht j hj)

/-- 同じ全体データからの二面は、共有する全成分上で整合する。 -/
lemma dgPartialSimplexHornFaceMap_compatible :
    horn.IsCompatible (dgPartialSimplexHornFaceMap t i ht) := by
  rw [horn.isCompatible_iff]
  intro j k hj hk hjk
  apply (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)).injective
  simp only [dgPartialSimplexHornFaceMap, SSet.stdSimplex.yonedaEquiv_δ_comp,
    Equiv.apply_symm_apply]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  change (t.pullback j.succAboveOrderEmb.toOrderHom).pullback
      (k.pred (Fin.ne_zero_of_lt hjk)).succAboveOrderEmb.toOrderHom =
    (t.pullback k.succAboveOrderEmb.toOrderHom).pullback
      (j.castPred (Fin.ne_last_of_lt hjk)).succAboveOrderEmb.toOrderHom
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Reindex.pullback_comp]
  apply congrArg t.pullback
  have he := SimplexCategory.δ_comp_δ' (i := j.castPred (Fin.ne_last_of_lt hjk))
    (j := k) (by simpa only [Fin.castSucc_castPred] using hjk)
  have ho := congrArg SimplexCategory.Hom.toOrderHom he
  simp only [Fin.castSucc_castPred] at ho
  exact ho.symm

/-- 既知方程式を持つ同じ全体データから貼り合わせた実ホーン。 -/
def dgPartialSimplexHorn : (Λ[n + 2, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D :=
  (dgPartialSimplexHornFaceMap_compatible t i ht).desc

/-- 貼ったホーンの各指定面は、同じ全体データの同じ面である。 -/
lemma dgPartialSimplexHorn_face (j : Fin (n + 3)) (hj : j ≠ i) :
    horn.ι i j hj ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPartialSimplexHorn t i ht = dgPartialSimplexHornFaceMap t i ht j hj :=
  horn.IsCompatible.ι_desc (dgPartialSimplexHornFaceMap_compatible t i ht) j hj

/-- 新ホーンから回収した各既知面のデータは、入力全体データの同じ引き戻し。 -/
lemma dgPartialSimplexHorn_knownData_face (j : Fin (n + 3)) (hj : j ≠ i) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgPartialSimplexHorn t i ht)).pullback j.succAboveOrderEmb.toOrderHom =
      t.pullback j.succAboveOrderEmb.toOrderHom := by
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HornPartial.knownData_pullback_face _ j hj).trans ?_
  have he := congrArg (SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)) (dgPartialSimplexHorn_face t i ht j hj)
  rw [SSet.yonedaEquiv_comp, horn.yonedaEquiv_ι] at he
  simp only [dgPartialSimplexHornFaceMap, Equiv.apply_symm_apply] at he
  exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData he

end SerrePositivity.InfinityCategories.Project.DerivedCategories
