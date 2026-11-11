module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanShapeCommaOpposite

/-!
概要：反転から作った局所 Kan 添字の比較は元の添字への射影を保つ。
方針：slice と comma の fiber の反転同型の射影を計算し、右側の比較の式を移す。
規約：quasicategory 性を使わない射の厳密な等式。
使われ方：点ごとの余極限を同じ図式の余極限として移送する。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：局所添字の反転同型は元の添字への反転した射影を保つ。
方針：pullback の保存同型と因子の交換の射影公式。
規約：二つの射は K.op を値域とする。
使われ方：局所図式の反転の可換性。 -/
lemma kanLeftKanShapeOpIso_projection {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeOpIso δ c).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c) =
        SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeOpIso, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalSlicePullbackOpIso, Iso.trans_hom,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection]
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd, asIso_hom,
    pullback.lift_fst, Category.comp_id, PreservesPullback.iso_hom_fst]

/-- 概要：comma の fiber の反転同型は元の添字への射影を保つ。
方針：fiber の包含の反転と、底の同型に後合成した fiber の包含の計算。
規約：二重反転を元の K へ戻す射を右辺に保持する。
使われ方：oriented comma の fiber に移した図式の同定。 -/
lemma kanLeftCommaFiberIso_source {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaFiberIso δ c).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ =
        SSet.opFunctor.map
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c)) ≫
            (SSet.opFunctorCompOpFunctorIso.app K).hom := by
  rfl

/-- 概要：反転で作った比較は局所図式の元の添字への射影を保つ。
方針：両端の反転同型の射影公式と右側の比較の射影公式を合成する。
規約：K と C は任意の単体集合。
使われ方：余極限を同じ図式に対して添字変更する。 -/
lemma kanLeftKanShapeToCommaFiberViaOpposite_projection {K C : SSet.{u}}
    (δ : K ⟶ C) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeToCommaFiberViaOpposite δ c ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeToCommaFiberViaOpposite
  rw [Category.assoc, Category.assoc, Category.assoc, kanLeftCommaFiberIso_source]
  have hright := congrArg (SSet.opFunctor.map)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightKanShapeToUnitCommaFiber_projection
      (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c))
  rw [CategoryTheory.Functor.map_comp] at hright
  have hleft := congrArg (SSet.opFunctor.map) (kanLeftKanShapeOpIso_projection δ c)
  rw [CategoryTheory.Functor.map_comp] at hleft
  rw [← Category.assoc (SSet.opFunctor.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightKanShapeToUnitCommaFiber (SSet.opFunctor.map δ) (SSet.opObjEquiv.symm c))),
    hright]
  rw [← Category.assoc (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeOpIso δ c).hom), hleft]
  have h := SSet.opFunctorCompOpFunctorIso.hom.naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c)
  change SSet.opFunctor.map (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c)) ≫
    (SSet.opFunctorCompOpFunctorIso.app K).hom =
      (SSet.opFunctorCompOpFunctorIso.app (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanShape δ c)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanProjection δ c at h
  rw [h, Iso.inv_hom_id_assoc]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
