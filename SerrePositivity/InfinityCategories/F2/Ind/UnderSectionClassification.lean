module

public import SerrePositivity.InfinityCategories.F2.Ind.UnderSectionReconstruction
public import SerrePositivity.InfinityCategories.F2.Ind.SpanLeftFibrationComparison
public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDiagramJointFibration
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningEssentialSurjectivity
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorSpaceCurrying

/-!
概要：同じ積上の under 復元 span を、一つの大域分類同型へ移す。
方針：相対写像空間で比較を戻し、元の分類関手と元の共同図式の余単位を合成する。
規約：底全体の FunctorIso を構成し、各値の同型の選択で代用しない。
使われ方：元の coherent 前層図式と strict weighted nerve の分類の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {I : Type u} [Category.{u} I] {B E : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B ⊗ nerve I) [LeftFibration p]

local instance : Quasicategory (B ⊗ nerve I) :=
  quasicategory_of_innerFibration (CartesianMonoidalCategory.snd B (nerve I))

/-- 元の積上の復元 span が誘導する、元の二つの left fibration の分類頂点の同型。 -/
def underSectionClassificationVertexIso :
    VertexIso (leftFibrationInfinityVertex p)
      (leftFibrationInfinityVertex (underSectionWeightedProjection p)) := by
  let r := underSectionReconstruction p
  have : InnerFibration r.projection := r.projection_innerFibration
  exact leftFibrationVertexIsoOfSpan p (underSectionWeightedProjection p)
    r.projection r.left r.right r.left_projection r.right_projection
    r.left_equivalence r.right_equivalence

/-- 同じ積上の二つの共同分類図式の一つの大域同型。 -/
def underSectionClassificationIso :
    FunctorIso (leftStraighteningInfinityDiagram p)
      (leftStraighteningInfinityDiagram (underSectionWeightedProjection p)) := by
  have h := (underSectionClassificationVertexIso p).map
    (leftStraighteningInfinityMap (B ⊗ nerve I))
  rw [← leftStraighteningInfinityDiagram_vertex p,
    ← leftStraighteningInfinityDiagram_vertex (underSectionWeightedProjection p)] at h
  exact h

variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ PresheafInfinity C)

/-- 元の前層図式の共同評価と、同じ strict weighted nerve の共同分類の大域同型。 -/
def presheafDiagramWeightedJointIso :
    FunctorIso (leftStraighteningInfinityDiagram
      (underSectionWeightedProjection (presheafDiagramJointProjection F)))
      (presheafDiagramJointEvaluation F) :=
  (underSectionClassificationIso (presheafDiagramJointProjection F)).symm ≪≫
    leftStraighteningInfinityCounit (presheafDiagramJointEvaluation F)

/-- 同じ共同 weighted 分類を前層の coherent 図式として読む。 -/
def presheafDiagramWeightedClassification :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ PresheafInfinity C :=
  curry ((HomotopyLimits.uliftTensorIso.{u, u + 1} C.op (nerve I)).inv ≫
    leftStraighteningInfinityDiagram
      (underSectionWeightedProjection (presheafDiagramJointProjection F)))

/-- 共同分類の大域同型を curry すると、元の前層図式 F そのものを回収する。 -/
def presheafDiagramWeightedClassificationIso :
    FunctorIso (presheafDiagramWeightedClassification F) F := by
  have h := ((presheafDiagramWeightedJointIso F).precomp
    (HomotopyLimits.uliftTensorIso.{u, u + 1} C.op (nerve I)).inv).curry
  simp only [presheafDiagramJointEvaluation, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp, curry_uncurry] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Ind
