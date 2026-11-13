module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedParameterCylinderFunctor

/-!
概要：パラメータ付き円柱の両端と、端をまたぐ恒等族の評価。
方針：端の包含を豊穣関手とし、合成の単位律で元のパラメータ族を回収する。
規約：豊穣関手としての厳密な制限式。使われ方：Sp の円の評価と loop 図式の端点。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.EnrichedParameterCylinder
end SerrePositivity.KST.Spectra.EnrichedParameterCylinder
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder
variable (A : SSet.{u}) {C : Type v} [EnrichedCategory SSet.{u} C]

/-- 元の圏から円柱の左端への包含。 -/
def leftInclusion : EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) where
  obj X := ⟨false, X⟩
  map X Y := 𝟙 (X ⟶[SSet] Y)
  map_id X := Category.comp_id _
  map_comp X Y Z := by
    change eComp SSet X Y Z ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ eComp SSet X Y Z
    simp

/-- 元の圏から円柱の右端への包含。 -/
def rightInclusion : EnrichedFunctor SSet.{u} C (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.Object A C) where
  obj X := ⟨true, X⟩
  map X Y := 𝟙 (X ⟶[SSet] Y)
  map_id X := Category.comp_id _
  map_comp X Y Z := by
    change eComp SSet X Y Z ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ eComp SSet X Y Z
    simp

variable {D : Type w} [EnrichedCategory SSet.{u} D]
  (F G : EnrichedFunctor SSet.{u} C D)
  (η : GradedNatTrans (Center.ofBraidedObj A) F G)

/-- 評価の円柱の左端は、元の左の豊穣関手。 -/
lemma evaluationFunctor_left :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftInclusion A).comp SSet (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor A F G η) = F := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  change (𝟙 _ ≫ F.map X Y) ≫ 𝟙 _ = F.map X Y
  simp

/-- 評価の円柱の右端は、元の右の豊穣関手。 -/
lemma evaluationFunctor_right :
    (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.rightInclusion A).comp SSet (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor A F G η) = G := by
  apply EnrichedFunctor.ext SSet (fun _ ↦ rfl)
  intro X Y
  change (𝟙 _ ≫ G.map X Y) ≫ 𝟙 _ = G.map X Y
  simp

/-- 同じ対象の二つの端を結ぶ、恒等射を持つパラメータ族。 -/
def crossIdentity (X : C) :
    A ⟶ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.EnrichedParameterCylinderHom.hom A ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftInclusion A).obj X) ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.rightInclusion A).obj X) :=
  (ρ_ A).inv ≫ A ◁ eId SSet X

/-- 円柱の関手は、恒等族の上で元のパラメータ付き評価を厳密に回収する。 -/
lemma crossIdentity_evaluation (X : C) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.crossIdentity A X ≫
      (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor A F G η).map ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftInclusion A).obj X) ((_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.rightInclusion A).obj X) =
      η.app X := by
  change (ρ_ A).inv ≫ A ◁ eId SSet X ≫
    (η.app X ⊗ₘ G.map X X) ≫ eComp SSet (F.obj X) (G.obj X) (G.obj X) = _
  rw [whiskerLeft_comp_tensorHom_assoc, G.map_id, rightUnitor_inv_comp_tensorHom_assoc]
  exact (congrArg (fun k ↦ η.app X ≫ k) (e_comp_id SSet (F.obj X) (G.obj X))).trans
    (Category.comp_id _)

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.crossIdentity (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.crossIdentity := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.crossIdentity

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.crossIdentity_evaluation := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.crossIdentity_evaluation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.evaluationFunctor_left := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor_left

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.evaluationFunctor_right := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.evaluationFunctor_right

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.leftInclusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftInclusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.rightInclusion (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.rightInclusion := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.rightInclusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.leftInclusion._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftInclusion._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.leftInclusion._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftInclusion._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.EnrichedParameterCylinder.rightInclusion._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.rightInclusion._proof_1
