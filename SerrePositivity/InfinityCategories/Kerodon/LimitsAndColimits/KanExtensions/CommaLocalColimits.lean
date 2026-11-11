module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanShapeCommaProjection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitDiagramIso

/-!
概要：oriented comma の fiber の図式と左 Kan の局所図式の余極限の存在は同値。
方針：比較の単射性を円筒の外延性で証明し、前合成同値による余極限の移送を使う。
規約：K・C・標的 D は quasicategory。
使われ方：一般の関手の点ごとの余極限を cocartesian な置き換えの fiber に渡す。

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

/-- 概要：coslice から comma の fiber への比較は単射。
方針：comma の矢印の族から coslice の普遍錐を復元し、標的射影も復元する。
規約：充填性は使わない。
使われ方：前合成同値による余極限の存在の移送。 -/
instance kanRightKanShapeToUnitCommaFiber_mono {X Y : SSet.{u}}
    (G : Y ⟶ X) (x : X _⦋0⦌) : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightKanShapeToUnitCommaFiber G x) := by
  constructor
  intro A f g h
  apply pullback.hom_ext
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_injective
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftMappingSpacePrism_hom_ext
    · have hh := congrArg (fun z ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaUncurry (z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaSource G) x)) h
      simp only [Category.assoc] at hh
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightKanShapeToUnitCommaFiber_uncurry,
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightKanShapeToUnitCommaFiber_uncurry] at hh
      exact hh
    · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_fixed]
  · have hh := congrArg (fun z ↦ z ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x) h
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRightKanShapeToUnitCommaFiber_projection] using hh

/-- 概要：反転で作った左の局所添字の比較も単射。
方針：右側の比較の単射性を反転し、同型と合成する。
規約：K と C は任意の単体集合。
使われ方：同じ図式の余極限の存在を保ち反映する添字変更。 -/
instance kanLeftKanShapeToCommaFiberViaOpposite_mono {K C : SSet.{u}}
    (δ : K ⟶ C) (c : C _⦋0⦌) : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeToCommaFiberViaOpposite δ c) := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeToCommaFiberViaOpposite
  infer_instance

/-- 概要：左 Kan の局所余極限の存在は oriented comma の fiber の余極限の存在と同値。
方針：図式を保つ単射な前合成同値で余極限の存在を移送する。
規約：δ に fibration 性、F₀ に延長の存在を仮定しない。
使われ方：点ごとの仮定を相対 join の図式の存在定理へ入力する。 -/
lemma kanLeftCommaFiber_hasColimit_iff_local {K C D : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D]
    (δ : K ⟶ C) (F₀ : K ⟶ D) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_restrict_of_precompositionEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeToCommaFiberViaOpposite δ c)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeToCommaFiberViaOpposite_isPrecompositionEquivalence δ c)
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeToCommaFiberViaOpposite δ c ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaProjection δ) c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftCommaSource δ ≫ F₀) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c := by
    simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram] using
      congrArg (fun z ↦ z ≫ F₀) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeToCommaFiberViaOpposite_projection δ c)
  rw [he] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
