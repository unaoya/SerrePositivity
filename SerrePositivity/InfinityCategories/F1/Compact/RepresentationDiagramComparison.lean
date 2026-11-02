module

public import SerrePositivity.InfinityCategories.Core.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftUnstraightening
public import SerrePositivity.InfinityCategories.F1.Transport.LeftTransportRepresentation

/-!
概要：元の表現の比較を、厳密に等しい指定図式の unstraightening へ移す。
方針：図式の等式に沿って実際の比較射を移送する。
規約：同じ元の pointed 写像と底の射を保持する。
使われ方：元の宇宙変更図式そのものの余錐の fiber 写像への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {E B : SSet.{u + 1}} {p : E ⟶ B} [LeftFibration p]

/-- 指定された等しい図式の全空間へ、元の比較射そのものを移送する。 -/
def representationDiagramComparison (R : LeftTransportRepresentation p)
    (G : B ⟶ SpaceInfinity.{u}) (h : R.diagram = G) : E ⟶ leftUnstraightening G :=
  R.comparison ≫ eqToHom (congrArg leftUnstraightening h)

/-- 指定図式への移送は、同じ元の pointed 写像を保持する。 -/
lemma representationDiagramComparison_pointed (R : LeftTransportRepresentation p)
    (G : B ⟶ SpaceInfinity.{u}) (h : R.diagram = G) :
    representationDiagramComparison R G h ≫ pullback.fst pointedSpaceProjection G =
      R.pointedMap := by
  subst G
  simp only [representationDiagramComparison, eqToHom_refl, Category.comp_id]
  rfl

/-- 指定図式への移送も、同じ元の底の射を保持する。 -/
lemma representationDiagramComparison_projection (R : LeftTransportRepresentation p)
    (G : B ⟶ SpaceInfinity.{u}) (h : R.diagram = G) :
    representationDiagramComparison R G h ≫ leftUnstraighteningProjection G = p := by
  subst G
  simp only [representationDiagramComparison, eqToHom_refl, Category.comp_id]
  exact R.over_base

/-- 指定図式への実比較自身は全空間の前合成同値。 -/
lemma representationDiagramComparison_isPrecompositionEquivalence
    (R : LeftTransportRepresentation p) (G : B ⟶ SpaceInfinity.{u}) (h : R.diagram = G) :
    IsPrecompositionEquivalence (representationDiagramComparison R G h) := by
  subst G
  simp only [representationDiagramComparison, eqToHom_refl, Category.comp_id]
  exact R.isPrecompositionEquivalence

end SerrePositivity.InfinityCategories.F2.Compact
