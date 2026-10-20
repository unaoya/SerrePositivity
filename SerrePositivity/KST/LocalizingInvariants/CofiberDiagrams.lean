module

public import SerrePositivity.KST.LocalizingInvariants.CofiberSquareFamily
public import SerrePositivity.InfinityCategories.Stable.LoopDiagramArrows

/-!
概要：普遍 cofiber 四角形の全部分圏と底辺・右辺の評価。
方針：元の四角形の零角と押し出し条件を保持し、安定性で普遍錐の族も得る。
規約：選択済みの全 cofiber 族もこの全部分圏へ入る。使われ方：cofiber 回転の完全性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams

def Predicate {X : SSet.{u}} (v : ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) _⦋0⦌) : Prop :=
  IsZeroVertex (squareVertex (squareDiagram v) 0 1) ∧ IsPushoutSquare (squareDiagram v)

def space (X : SSet.{u}) : SSet.{u} :=
  (fullSubcomplexOnVertices ((ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X) Predicate : SSet.{u})

instance (X : SSet.{u}) [Quasicategory X] : Quasicategory (space X) :=
  fullSubcomplexOnVertices_quasicategory _ _

def inclusion (X : SSet.{u}) : space X ⟶ (ihom (Δ[1] ⊗ Δ[1] : SSet.{u})).obj X :=
  (fullSubcomplexOnVertices _ Predicate).ι

def bottom (X : SSet.{u}) : space X ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  inclusion X ≫ (pre squareBottomEdge).app X

def right (X : SSet.{u}) : space X ⟶ (ihom (Δ[1] : SSet.{u})).obj X :=
  inclusion X ≫ (pre squareRightEdge).app X

def left (X : SSet.{u}) : space X ⟶ zeroTargetArrows X :=
  fullSubcomplexLift IsZeroTargetArrow (inclusion X ≫ (pre squareLeftEdge).app X) (by
    intro v
    have hv := (fullSubcomplexOnVertices_vertex v).1
    have he : functorVertex (squareDiagram v.val) = v.val :=
      (functorVertexEquiv _ _).apply_symm_apply _
    change IsZeroTargetArrow (((pre squareLeftEdge).app X).app _ v.val)
    rw [← he]
    change IsZeroTargetArrow (functorVertex (squareLeftEdge ≫ squareDiagram v.val))
    unfold IsZeroTargetArrow
    rw [evaluateFunctorAt_functorVertex]
    exact hv)

def top (X : SSet.{u}) : space X ⟶ zeroSourceArrows X :=
  fullSubcomplexLift IsZeroSourceArrow (inclusion X ≫ (pre squareTopEdge).app X) (by
    intro v
    have hv := (fullSubcomplexOnVertices_vertex v).1
    have he : functorVertex (squareDiagram v.val) = v.val :=
      (functorVertexEquiv _ _).apply_symm_apply _
    change IsZeroSourceArrow (((pre squareTopEdge).app X).app _ v.val)
    rw [← he]
    change IsZeroSourceArrow (functorVertex (squareTopEdge ≫ squareDiagram v.val))
    unfold IsZeroSourceArrow
    rw [evaluateFunctorAt_functorVertex]
    exact hv)

lemma bottom_source (X : SSet.{u}) : bottom X ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      left X ≫ zeroTargetArrowSource X := by
  rw [bottom, zeroTargetArrowSource, ← Category.assoc (left X), left,
    fullSubcomplexLift_ι]
  simp only [Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

lemma right_target (X : SSet.{u}) : right X ≫
    evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      top X ≫ zeroSourceArrowTarget X := by
  rw [right, zeroSourceArrowTarget, ← Category.assoc (top X), top,
    fullSubcomplexLift_ι]
  simp only [Category.assoc, stable_pre_evaluateFunctorAt]
  rfl

def cocones (X : SSet.{u}) [Quasicategory X] : space X ⟶ colimitCocones (horn 2 0 : SSet.{u}) X :=
  fullSubcomplexLift (InitialBoundaryLifting (coconeRestriction (horn 2 0 : SSet.{u}) X))
    (inclusion X ≫ (pre spanCoconeSquareIso.hom).app X) (by
    intro v
    have hp := (fullSubcomplexOnVertices_vertex v).2
    have he : functorVertex (squareDiagram v.val) = v.val :=
      (functorVertexEquiv _ _).apply_symm_apply _
    change InitialBoundaryLifting _ (((pre spanCoconeSquareIso.hom).app X).app _ v.val)
    rw [← he]
    exact hp.initialBoundaryLifting)

lemma cocones_inclusion (X : SSet.{u}) [Quasicategory X] : cocones X ≫
    (relativeInitialVertices (coconeRestriction (horn 2 0 : SSet.{u}) X)).ι =
      inclusion X ≫ (pre spanCoconeSquareIso.hom).app X := rfl

lemma cocones_projection (X : SSet.{u}) [Quasicategory X] : cocones X ≫
    colimitCoconeProjection (horn 2 0 : SSet.{u}) X =
      inclusion X ≫ (pre spanSquareBoundary).app X := by
  change (cocones X ≫ (relativeInitialVertices (coconeRestriction _ X)).ι) ≫
    (pre (joinInl _ Δ[0])).app X = _
  rw [cocones_inclusion, Category.assoc, ← NatTrans.comp_app, ← pre_map]
  rfl

def cones (X : SSet.{u}) [Quasicategory X] [IsStable X] :
    space X ⟶ limitCones (horn 2 2 : SSet.{u}) X :=
  fullSubcomplexLift (TerminalBoundaryLifting (coneRestriction (horn 2 2 : SSet.{u}) X))
    (inclusion X ≫ (pre cospanConeSquareIso.hom).app X) (by
    intro v
    have hv := fullSubcomplexOnVertices_vertex v
    have hp := IsStable.pullback_of_pushout (⟨squareDiagram v.val, hv.1⟩ : ZeroTriangle X) hv.2
    have he : functorVertex (squareDiagram v.val) = v.val :=
      (functorVertexEquiv _ _).apply_symm_apply _
    change TerminalBoundaryLifting _ (((pre cospanConeSquareIso.hom).app X).app _ v.val)
    rw [← he]
    exact terminalBoundaryLifting_coneRestriction_of_isLimitCone
      (pullbackCone (squareDiagram v.val)) hp)

lemma cones_inclusion (X : SSet.{u}) [Quasicategory X] [IsStable X] : cones X ≫
    (relativeTerminalVertices (coneRestriction (horn 2 2 : SSet.{u}) X)).ι =
      inclusion X ≫ (pre cospanConeSquareIso.hom).app X := rfl

lemma cones_projection (X : SSet.{u}) [Quasicategory X] [IsStable X] : cones X ≫
    limitConeProjection (horn 2 2 : SSet.{u}) X =
      inclusion X ≫ (pre cospanSquareBoundary).app X := by
  change (cones X ≫ (relativeTerminalVertices (coneRestriction _ X)).ι) ≫
    (pre (joinInr Δ[0] _)).app X = _
  rw [cones_inclusion, Category.assoc, ← NatTrans.comp_app, ← pre_map]
  rfl

end SerrePositivity.KST.LocalizingInvariants.CofiberDiagrams
