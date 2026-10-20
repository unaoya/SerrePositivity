module

public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeNativeUniversalFaces
public import SerrePositivity.InfinityCategories.HomotopyLimits.CosliceEdgeFamilyNaturality

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
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "d" => partialColimitSpecifiedPathCocone hp p c hc dB dC
local notation "T" => pinchedHomLeft (JoinCocone.vertex d) y
local notation "root" => specifiedCoconeNativeRootEdge hp p c hc dB dC
local notation "Q" => Iso.inv (leftFibrationInitialBaseIso (sliceUnderProjection p) d y)
local notation "rt" => specifiedCoconeNativeRootEdge_target hp p c hc dB dC
local notation "Qraw" => Q ≫ eqToHom
  (congrArg (fun a ↦ coconeMappingSpace a y) (Eq.symm rt))

section
local notation "σ" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "H" => specifiedCoconeLeftNativeUniversalComparison hp p c hc dB dC y
local notation "HA" => specifiedCoconeLeftNativeUniversalAttachmentFace hp p c hc dB dC y
local notation "HR" => specifiedCoconeLeftNativeUniversalRootFace hp p c hc dB dC y
local notation "e" => colimitAttachmentRestrictionEdge c hc f (i ≫ p) rfl dB
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "face" => stdSimplex.δ (2 : Fin 3)
local notation "af" => specifiedCoconeLeftNativeBaseDiagram_attachment hp p c hc dB dC
local notation "mid" => normalizedCoconeRestrictionFiber σ ((stdSimplex.δ (0 : Fin 2)) ≫ face)
  (Eq.trans (Category.assoc _ _ _) (congrArg (stdSimplex.δ (0 : Fin 2) ≫ ·) af)) y

/-- 左の元の付加辺面比較と native 普遍族の比較を、同じ面円柱を保つ正方形へ束ねる。 -/
def specifiedCoconeLeftNativeUniversalAttachmentSquare :=
  cosliceEdgeFamilyNaturalitySquare (t ≫ q) y HA

/-- 左の元の根辺比較と native 普遍族の比較も、同じ根辺円柱を保つ正方形へ束ねる。 -/
def specifiedCoconeLeftNativeUniversalRootSquare :=
  cosliceEdgeFamilyNaturalitySquare root y HR

/-- 付加辺面の切断像の側辺は、同じ全族間円柱の動く中頂点を切断で戻した raw な射。 -/
lemma specifiedCoconeLeftNativeUniversalAttachmentSection_raw :
    (cosliceEdgeFamilySectionHomotopy (t ≫ q) y HA).h =
      (H).h ≫ mid ≫ cosliceEdgeSectionFiber (t ≫ q) y := by
  rw [cosliceEdgeFamilySectionHomotopy_raw]
  exact (Category.assoc (HA).h
    (cosliceRestrictionFiberMap (t ≫ q) (stdSimplex.δ (0 : Fin 2)) y)
    (cosliceEdgeSectionFiber (t ≫ q) y)).symm.trans
      ((congrArg (· ≫ cosliceEdgeSectionFiber (t ≫ q) y)
        (specifiedCoconeLeftNativeUniversalAttachmentFace_terminal hp p c hc dB dC y)).trans
          (Category.assoc _ _ _))

/-- 根辺面の切断像の側辺は、元の同じ終端係数の切断像で全時刻定値である。 -/
lemma specifiedCoconeLeftNativeUniversalRootSection_raw :
    (cosliceEdgeFamilySectionHomotopy root y HR).h =
      fst T Δ[1] ≫ Qraw ≫ cosliceEdgeSectionFiber root y := by
  have hterm := congrArg (· ≫
      eqToHom (congrArg (fun a ↦ coconeMappingSpace a y) (Eq.symm rt)))
    (specifiedCoconeLeftNativeUniversalRootFace_terminal hp p c hc dB dC y)
  rw [normalizedCoconeRestrictionFiber_eq root (stdSimplex.δ (0 : Fin 2)) rt y] at hterm
  have hraw : (HR).h ≫ cosliceRestrictionFiberMap root (stdSimplex.δ (0 : Fin 2)) y =
      fst T Δ[1] ≫ Qraw := by
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hterm
  rw [cosliceEdgeFamilySectionHomotopy_raw]
  exact (Category.assoc (HR).h
    (cosliceRestrictionFiberMap root (stdSimplex.δ (0 : Fin 2)) y)
    (cosliceEdgeSectionFiber root y)).symm.trans
      ((congrArg (· ≫ cosliceEdgeSectionFiber root y) hraw).trans (Category.assoc _ _ _))

/-- 根辺正方形の切断像側辺の類は、元の同じ終端族の切断像の恒等射である。 -/
lemma specifiedCoconeLeftNativeUniversalRootSection_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (cosliceEdgeFamilySectionHomotopy root y HR))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk
        (functorVertex (Qraw ≫ cosliceEdgeSectionFiber root y)))) := by
  have h := kanFunctorHomotopy_hom_arrow_of_h_eq (cosliceEdgeFamilySectionHomotopy root y HR)
    (functorHomotopyRefl (Qraw ≫ cosliceEdgeSectionFiber root y))
    (specifiedCoconeLeftNativeUniversalRootSection_raw hp p c hc dB dC y)
  rw [functorHomotopyRefl_hom] at h
  exact h
end

section
local notation "σ" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "H" => specifiedCoconeRightNativeUniversalComparison hp p c hc dB dC y
local notation "HA" => specifiedCoconeRightNativeUniversalAttachmentFace hp p c hc dB dC y
local notation "HR" => specifiedCoconeRightNativeUniversalRootFace hp p c hc dB dC y
local notation "e" => colimitAttachmentRestrictionEdge c hc g (j ≫ p)
    (coconePushoutBoundary_eq hp p) dC
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "face" => stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)
local notation "af" => specifiedCoconeRightNativeBaseDiagram_attachment hp p c hc dB dC
local notation "mid" => normalizedCoconeRestrictionFiber σ ((stdSimplex.δ (0 : Fin 2)) ≫ face)
  (Eq.trans (Category.assoc _ _ _) (congrArg (stdSimplex.δ (0 : Fin 2) ≫ ·) af)) y

/-- 右の元の付加辺面比較と native 普遍族の比較を、同じ面円柱を保つ正方形へ束ねる。 -/
def specifiedCoconeRightNativeUniversalAttachmentSquare :=
  cosliceEdgeFamilyNaturalitySquare (t ≫ q) y HA

/-- 右の元の根辺比較と native 普遍族の比較も、同じ根辺円柱を保つ正方形へ束ねる。 -/
def specifiedCoconeRightNativeUniversalRootSquare :=
  cosliceEdgeFamilyNaturalitySquare root y HR

/-- 付加辺面の切断像の側辺は、同じ全族間円柱の動く中頂点を切断で戻した raw な射。 -/
lemma specifiedCoconeRightNativeUniversalAttachmentSection_raw :
    (cosliceEdgeFamilySectionHomotopy (t ≫ q) y HA).h =
      (H).h ≫ mid ≫ cosliceEdgeSectionFiber (t ≫ q) y := by
  rw [cosliceEdgeFamilySectionHomotopy_raw]
  exact (Category.assoc (HA).h
    (cosliceRestrictionFiberMap (t ≫ q) (stdSimplex.δ (0 : Fin 2)) y)
    (cosliceEdgeSectionFiber (t ≫ q) y)).symm.trans
      ((congrArg (· ≫ cosliceEdgeSectionFiber (t ≫ q) y)
        (specifiedCoconeRightNativeUniversalAttachmentFace_terminal hp p c hc dB dC y)).trans
          (Category.assoc _ _ _))

/-- 根辺面の切断像の側辺は、元の同じ終端係数の切断像で全時刻定値である。 -/
lemma specifiedCoconeRightNativeUniversalRootSection_raw :
    (cosliceEdgeFamilySectionHomotopy root y HR).h =
      fst T Δ[1] ≫ Qraw ≫ cosliceEdgeSectionFiber root y := by
  have hterm := congrArg (· ≫
      eqToHom (congrArg (fun a ↦ coconeMappingSpace a y) (Eq.symm rt)))
    (specifiedCoconeRightNativeUniversalRootFace_terminal hp p c hc dB dC y)
  rw [normalizedCoconeRestrictionFiber_eq root (stdSimplex.δ (0 : Fin 2)) rt y] at hterm
  have hraw : (HR).h ≫ cosliceRestrictionFiberMap root (stdSimplex.δ (0 : Fin 2)) y =
      fst T Δ[1] ≫ Qraw := by
    simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using hterm
  rw [cosliceEdgeFamilySectionHomotopy_raw]
  exact (Category.assoc (HR).h
    (cosliceRestrictionFiberMap root (stdSimplex.δ (0 : Fin 2)) y)
    (cosliceEdgeSectionFiber root y)).symm.trans
      ((congrArg (· ≫ cosliceEdgeSectionFiber root y) hraw).trans (Category.assoc _ _ _))

/-- 根辺正方形の切断像側辺の類は、元の同じ終端族の切断像の恒等射である。 -/
lemma specifiedCoconeRightNativeUniversalRootSection_hom_arrow :
    Arrow.mk (SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (cosliceEdgeFamilySectionHomotopy root y HR))) =
      Arrow.mk (𝟙 (HomotopyCategory.mk
        (functorVertex (Qraw ≫ cosliceEdgeSectionFiber root y)))) := by
  have h := kanFunctorHomotopy_hom_arrow_of_h_eq (cosliceEdgeFamilySectionHomotopy root y HR)
    (functorHomotopyRefl (Qraw ≫ cosliceEdgeSectionFiber root y))
    (specifiedCoconeRightNativeUniversalRootSection_raw hp p c hc dB dC y)
  rw [functorHomotopyRefl_hom] at h
  exact h
end

end
end SerrePositivity.InfinityCategories.HomotopyLimits
