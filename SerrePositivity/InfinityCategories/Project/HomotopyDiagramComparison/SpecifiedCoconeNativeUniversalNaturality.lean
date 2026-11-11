module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeNativeUniversalFaces
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceEdgeFamilyNaturality

/-!
概要：元の二面と native 普遍全族の二面の切断比較を、同じ四辺の自然性正方形へ束ねる。
方針：元の全族間円柱の面を使い、付加辺の動く終端と根辺の定値終端を厳密に計算する。
規約：終端の切断像も同じ円柱から作る。使われ方：元の native 指定経路と共通 end の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "d" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex d) y
local notation "root" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "Q" => Iso.inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialBaseIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) d y)
local notation "rt" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge_target hp p c hc dB dC
local notation "Qraw" => Q ≫ eqToHom
  (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y) (Eq.symm rt))

section
local notation "σ" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeUniversalComparison hp p c hc dB dC y
local notation "HA" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeUniversalAttachmentFace hp p c hc dB dC y
local notation "HR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeUniversalRootFace hp p c hc dB dC y
local notation "e" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentRestrictionEdge c hc f (i ≫ p) rfl dB
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "face" => stdSimplex.δ (2 : Fin 3)
local notation "af" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeBaseDiagram_attachment hp p c hc dB dC
local notation "mid" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ ((stdSimplex.δ (0 : Fin 2)) ≫ face)
  (Eq.trans (Category.assoc _ _ _) (congrArg (stdSimplex.δ (0 : Fin 2) ≫ ·) af)) y

/-- 左の元の付加辺面比較と native 普遍族の比較を、同じ面円柱を保つ正方形へ束ねる。 -/
def specifiedCoconeLeftNativeUniversalAttachmentSquare :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyNaturalitySquare (t ≫ q) y HA

/-- 左の元の根辺比較と native 普遍族の比較も、同じ根辺円柱を保つ正方形へ束ねる。 -/
def specifiedCoconeLeftNativeUniversalRootSquare :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyNaturalitySquare root y HR

/-- 付加辺面の切断像の側辺は、同じ全族間円柱の動く中頂点を切断で戻した raw な射。 -/
lemma specifiedCoconeLeftNativeUniversalAttachmentSection_raw :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilySectionHomotopy (t ≫ q) y HA).h =
      (H).h ≫ mid ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber (t ≫ q) y := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilySectionHomotopy_raw]
  exact (Category.assoc (HA).h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (t ≫ q) (stdSimplex.δ (0 : Fin 2)) y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber (t ≫ q) y)).symm.trans
      ((congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber (t ≫ q) y)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeUniversalAttachmentFace_terminal hp p c hc dB dC y)).trans
          (Category.assoc _ _ _))

/-- 根辺面の切断像の側辺は、元の同じ終端係数の切断像で全時刻定値である。 -/
lemma specifiedCoconeLeftNativeUniversalRootSection_raw :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilySectionHomotopy root y HR).h =
      fst T Δ[1] ≫ Qraw ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber root y := by
  have hterm := congrArg (· ≫
      eqToHom (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y) (Eq.symm rt)))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftNativeUniversalRootFace_terminal hp p c hc dB dC y)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber_eq root (stdSimplex.δ (0 : Fin 2)) rt y] at hterm
  have hraw : (HR).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap root (stdSimplex.δ (0 : Fin 2)) y =
      fst T Δ[1] ≫ Qraw := by
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hterm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilySectionHomotopy_raw]
  exact (Category.assoc (HR).h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap root (stdSimplex.δ (0 : Fin 2)) y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber root y)).symm.trans
      ((congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber root y) hraw).trans (Category.assoc _ _ _))

/-- 根辺正方形の切断像側辺の類は、元の同じ終端族の切断像の恒等射である。 -/
lemma specifiedCoconeLeftNativeUniversalRootSection_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilySectionHomotopy root y HR))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (Qraw ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber root y)))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilySectionHomotopy root y HR)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (Qraw ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber root y))
    (specifiedCoconeLeftNativeUniversalRootSection_raw hp p c hc dB dC y)
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom] at h
  exact h
end

section
local notation "σ" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "H" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeUniversalComparison hp p c hc dB dC y
local notation "HA" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeUniversalAttachmentFace hp p c hc dB dC y
local notation "HR" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeUniversalRootFace hp p c hc dB dC y
local notation "e" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentRestrictionEdge c hc g (j ≫ p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "face" => stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)
local notation "af" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeBaseDiagram_attachment hp p c hc dB dC
local notation "mid" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ ((stdSimplex.δ (0 : Fin 2)) ≫ face)
  (Eq.trans (Category.assoc _ _ _) (congrArg (stdSimplex.δ (0 : Fin 2) ≫ ·) af)) y

/-- 右の元の付加辺面比較と native 普遍族の比較を、同じ面円柱を保つ正方形へ束ねる。 -/
def specifiedCoconeRightNativeUniversalAttachmentSquare :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyNaturalitySquare (t ≫ q) y HA

/-- 右の元の根辺比較と native 普遍族の比較も、同じ根辺円柱を保つ正方形へ束ねる。 -/
def specifiedCoconeRightNativeUniversalRootSquare :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilyNaturalitySquare root y HR

/-- 付加辺面の切断像の側辺は、同じ全族間円柱の動く中頂点を切断で戻した raw な射。 -/
lemma specifiedCoconeRightNativeUniversalAttachmentSection_raw :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilySectionHomotopy (t ≫ q) y HA).h =
      (H).h ≫ mid ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber (t ≫ q) y := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilySectionHomotopy_raw]
  exact (Category.assoc (HA).h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap (t ≫ q) (stdSimplex.δ (0 : Fin 2)) y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber (t ≫ q) y)).symm.trans
      ((congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber (t ≫ q) y)
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeUniversalAttachmentFace_terminal hp p c hc dB dC y)).trans
          (Category.assoc _ _ _))

/-- 根辺面の切断像の側辺は、元の同じ終端係数の切断像で全時刻定値である。 -/
lemma specifiedCoconeRightNativeUniversalRootSection_raw :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilySectionHomotopy root y HR).h =
      fst T Δ[1] ≫ Qraw ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber root y := by
  have hterm := congrArg (· ≫
      eqToHom (congrArg (fun a ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace a y) (Eq.symm rt)))
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightNativeUniversalRootFace_terminal hp p c hc dB dC y)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber_eq root (stdSimplex.δ (0 : Fin 2)) rt y] at hterm
  have hraw : (HR).h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap root (stdSimplex.δ (0 : Fin 2)) y =
      fst T Δ[1] ≫ Qraw := by
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hterm
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilySectionHomotopy_raw]
  exact (Category.assoc (HR).h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap root (stdSimplex.δ (0 : Fin 2)) y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber root y)).symm.trans
      ((congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber root y) hraw).trans (Category.assoc _ _ _))

/-- 根辺正方形の切断像側辺の類は、元の同じ終端族の切断像の恒等射である。 -/
lemma specifiedCoconeRightNativeUniversalRootSection_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilySectionHomotopy root y HR))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (Qraw ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber root y)))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeFamilySectionHomotopy root y HR)
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl (Qraw ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.cosliceEdgeSectionFiber root y))
    (specifiedCoconeRightNativeUniversalRootSection_raw hp p c hc dB dC y)
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyRefl_hom] at h
  exact h
end

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
