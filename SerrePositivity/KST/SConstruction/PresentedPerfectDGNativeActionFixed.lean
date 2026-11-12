module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGNativeAction
public import SerrePositivity.KST.SConstruction.DGNativePointSimplex

/-! # 元の厳密 dg 入力に固定した native Perf 作用の回収
概要：全関手族の実 Perf 右作用を元の dg 関手に固定すると、元の実 Perf 作用へ戻る。
方針：元の定数単体との tensor は実包含であり、実右作用の同じ包含への制限を使う。
規約：零単体だけでなく全 Perf 単体を回収。使われ方：安定性と完全性への接続。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [DGCategory A E] [Small.{u} D] [Small.{u} E]

/-- 元の固定入力の全定数単体による作用は、元の Perf dg 関手の全単体作用。 -/
lemma presentedPerfectDGNativeActionSimplex_fixed {N : ℕ}
    (x : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A (PresentedPerfectDGObject A D) N) (F : DGFunctor A D E) :
    presentedPerfectDGNativeActionSimplex A D E x
        (dgNativePointSimplex A (DGFunctor A D E) F N) =
      x.map (presentedPerfectDGAction A D E F) := by
  unfold presentedPerfectDGNativeActionSimplex
  rw [dgNerveTensorSimplex_point_right]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  change (x.toSimplexData.map _).map _ = x.toSimplexData.map _
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.SimplexData.map_comp, presentedPerfectDGRightTensorAction_fixed]

/-- 元の厳密 dg 関手を、出力宇宙へ移した Kan 入力写像空間の単位射として保持。 -/
def presentedPerfectDGNativeParameterPoint (F : DGFunctor A D E) :
    𝟙_ SSet.{max (u + 1) v} ⟶ presentedPerfectDGNativeParameter A D E :=
  (SSet.unitHomEquiv (presentedPerfectDGNativeParameter A D E)).symm
    (ULift.up (dgFunctorNativeMappingVertex A D E F))

omit [Small.{u} E] in
/-- 元の入力関手の単位射の全次数は、元の閉単位による同じ native 定数単体。 -/
lemma presentedPerfectDGNativeParameterPoint_app (F : DGFunctor A D E)
    (n : SimplexCategoryᵒᵖ) (x : (𝟙_ SSet.{max (u + 1) v}).obj n) :
    (((presentedPerfectDGNativeParameterPoint A D E F).app n x).down).val =
      dgNativePointSimplex A (DGFunctor A D E) F n.unop.len := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex F).pullback
    (SimplexCategory.const n.unop ⦋0⦌ 0).toOrderHom = _
  rw [← dgNativePointSimplex_zero]
  exact dgNativePointSimplex_pullback A (DGFunctor A D E) F _

/-- 元の入力関手に固定した実右作用は、元の Perf 作用の単体的写像を厳密に回収。 -/
lemma presentedPerfectDGNativeCoreAction_fixed (F : DGFunctor A D E) :
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D)) ⊗ₘ
        presentedPerfectDGNativeParameterPoint A D E F) ≫
        presentedPerfectDGNativeCoreAction A D E =
      (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A (PresentedPerfectDGObject A D))).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A D E F) := by
  ext n p
  rcases p with ⟨x, a⟩
  change presentedPerfectDGNativeActionSimplex A D E x
      (((presentedPerfectDGNativeParameterPoint A D E F).app n a).down.val) =
    x.map (presentedPerfectDGAction A D E F)
  rw [presentedPerfectDGNativeParameterPoint_app]
  exact presentedPerfectDGNativeActionSimplex_fixed A D E x F

/-- 関手空間への実射を元の入力に固定すると、元の Perf 関手の curry を回収する。 -/
lemma presentedPerfectDGNativeFamilyMap_fixed (F : DGFunctor A D E) :
    presentedPerfectDGNativeParameterPoint A D E F ≫ presentedPerfectDGNativeFamilyMap A D E =
      curry' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (presentedPerfectDGAction A D E F)) := by
  rw [presentedPerfectDGNativeFamilyMap, ← curry_natural_left, curry', ← id_tensorHom,
    presentedPerfectDGNativeCoreAction_fixed]

end SerrePositivity.KST.SConstruction
