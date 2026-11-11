module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PushoutTopMappingFiber
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SpanCoconeMappingPullback
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.VertexFiberIsPullbackIso

/-!
概要：pushout の右枝上の指定 fiber を、左枝の始点制限の指定 fiber に同定する。
方針：span の余錐空間の厳密な引き戻しを、右枝の図式表示の同型で移す。
規約：固定終点と指定右枝余錐を保持し、元の左枝の全空間に結論する。
使われ方：HTT 5.5.5.13 の元の二辺に対する fiber の比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {C : SSet.{u}} (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ C)

/-- 入力 span の右枝は、元の四角形の左辺そのもの。 -/
lemma pushoutSpan_rightDiagram : horn₂₀.ι₀₂ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ R := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanSquareBoundary_leftEdge]

/-- 元の右枝余錐を、入力 span の左枝の始点に制限する。 -/
def pushoutSpanRightBase (y : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ R) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (stdSimplex.δ (1 : Fin 2) ≫ horn₂₀.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R) y :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberDiagramIso (pushoutSpan_rightDiagram R) y).inv ≫
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanCoconeMappingRightBase (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R) y

/-- 元の同じ図式の表示で、span の余錐空間は依然として厳密な引き戻しとなる。 -/
lemma pushoutSpanMapping_isPullback (y : C _⦋0⦌) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R) horn₂₀.ι₀₁ y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pushoutSpanRightMappingRestriction R y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (horn₂₀.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R) (stdSimplex.δ (1 : Fin 2)) y)
      (pushoutSpanRightBase R y) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberDiagramIso (pushoutSpan_rightDiagram R) y
  apply (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.spanCoconeMapping_isPullback (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R) y).of_iso
    (Iso.refl _) (Iso.refl _) e (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pushoutSpanRightMappingRestriction,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber_eq, e, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceFiberDiagramIso, eqToIso.hom]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
  · simp only [Iso.refl_hom, Category.comp_id, pushoutSpanRightBase, e,
      ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- 右枝上の同じ指定 fiber は、元の左枝の始点制限の同じ fiber と厳密に同型。 -/
def pushoutSpanSourceFiberIso (y : C _⦋0⦌)
    (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ R) y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pushoutSpanRightMappingRestriction R y) d ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (horn₂₀.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R)
        (stdSimplex.δ (1 : Fin 2)) y) ((pushoutSpanRightBase R y).app _ d) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.vertexFiberIsoOfIsPullback (pushoutSpanMapping_isPullback R y) d

/-- 元の左枝の指定 fiber の可縮性は、上辺の指定 fiber の可縮性と一致する。 -/
lemma pushoutSourceFiber_contractible_iff [Quasicategory C]
    (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare R) (y : C _⦋0⦌)
    (d : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ R) y) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (horn₂₀.ι₀₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan R)
      (stdSimplex.δ (1 : Fin 2)) y) ((pushoutSpanRightBase R y).app _ d)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.squareTopSourceMappingRestriction R y)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ R) (stdSimplex.δ (0 : Fin 2)) y).app _ d)) := by
  constructor
  · intro h
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pushoutMappingFiber_contractible_iff R hR y d).mp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (pushoutSpanSourceFiberIso R y d).symm h)
  · intro h
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (pushoutSpanSourceFiberIso R y d)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pushoutMappingFiber_contractible_iff R hR y d).mpr h)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
