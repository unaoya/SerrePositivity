module
public import SerrePositivity.KST.Spectra.PointedEnrichment
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.EnrichedMappingLaws

/-! # 点つき写像のパラメーター族の合成
概要：点つき内部 Hom の合成を、既存の頂点表示と前後合成へ接続する。
方針：L9 の単体的豊穣と通常の射との整合性を使う。
規約：局所的な豊穣 instance を使い、他レーンの定義を変更しない。
使われ方：逆射と Kan 延長を合成する随伴構造射の全パラメーター族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open Spectra Spectra.PointedMapping
open scoped Simplicial
local instance : SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 点つき写像空間の実際の単体的合成。 -/
def pointedMappingComposition (X Y Z : PointedSimplicialSet.{u}) :
    (PointedObject.basedHom X Y).right ⊗ (PointedObject.basedHom Y Z).right ⟶
      (PointedObject.basedHom X Z).right := eComp SSet X Y Z

/-- 合成の頂点は通常の点つき射の合成を表す。 -/
lemma pointedMappingComposition_vertex {X Y Z : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (pointedMappingComposition X Y Z).app (Opposite.op ⦋0⦌) (familyVertex f, familyVertex g) =
      familyVertex (f ≫ g) := by
  simp only [familyVertex_eq_pointedHomVertex]
  have h := congrArg (SSet.unitHomEquiv (SimplicialCategory.sHom X Z)) (eHomEquiv_comp SSet f g)
  exact h.symm

/-- 合成する族の源の制限を合成の前へ移せる。 -/
lemma pointedMappingComposition_pre {X X' Y Z : PointedSimplicialSet.{u}} (a : X' ⟶ X) :
    pointedMappingComposition X Y Z ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Z).right =
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Y).right ▷ (PointedObject.basedHom Y Z).right ≫
        pointedMappingComposition X' Y Z := by
  have h := eComp_eHomWhiskerRight SSet a Y Z
  rw [PointedEnrichment.whiskerRight_eq, PointedEnrichment.whiskerRight_eq] at h
  exact h

/-- 合成する族の標的の後合成を合成の前へ移せる。 -/
lemma pointedMappingComposition_post {X Y Z Z' : PointedSimplicialSet.{u}} (b : Z ⟶ Z') :
    pointedMappingComposition X Y Z ≫ (PointedObject.basedHomMap X b).right =
      (PointedObject.basedHom X Y).right ◁ (PointedObject.basedHomMap Y b).right ≫
        pointedMappingComposition X Y Z' := by
  have h := eComp_eHomWhiskerLeft SSet X Y b
  rw [PointedEnrichment.whiskerLeft_eq, PointedEnrichment.whiskerLeft_eq] at h
  exact h

/-- 中間の通常の射は合成する二つのパラメーター族の間で移せる。 -/
lemma pointedMappingComposition_middle {X Y Y' Z : PointedSimplicialSet.{u}} (a : Y ⟶ Y') :
    (PointedObject.basedHomMap X a).right ▷ (PointedObject.basedHom Y' Z).right ≫
      pointedMappingComposition X Y' Z =
    (PointedObject.basedHom X Y).right ◁ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Z).right ≫
      pointedMappingComposition X Y Z := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.enriched_comp_middle SSet X a Z
  rw [PointedEnrichment.whiskerLeft_eq, PointedEnrichment.whiskerRight_eq] at h
  exact h

/-- 独立な二つのパラメーター族の間で、中間の射を厳密に移せる。 -/
lemma pointedMappingComposition_families_middle {P Q : SSet.{u}}
    {X Y Y' Z : PointedSimplicialSet.{u}}
    (f : P ⟶ (PointedObject.basedHom X Y).right)
    (g : Q ⟶ (PointedObject.basedHom Y' Z).right) (a : Y ⟶ Y') :
    ((f ≫ (PointedObject.basedHomMap X a).right) ⊗ₘ g) ≫
        pointedMappingComposition X Y' Z =
      (f ⊗ₘ (g ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Z).right)) ≫ pointedMappingComposition X Y Z := by
  rw [← tensorHom_comp_whiskerRight, Category.assoc, pointedMappingComposition_middle,
    ← Category.assoc, tensorHom_comp_whiskerLeft]

/-- 合成族の後合成を第二の因子へ移せる。 -/
lemma pointedMappingComposition_families_post {P Q : SSet.{u}}
    {X Y Z Z' : PointedSimplicialSet.{u}}
    (f : P ⟶ (PointedObject.basedHom X Y).right)
    (g : Q ⟶ (PointedObject.basedHom Y Z).right) (b : Z ⟶ Z') :
    (f ⊗ₘ (g ≫ (PointedObject.basedHomMap Y b).right)) ≫
        pointedMappingComposition X Y Z' =
      ((f ⊗ₘ g) ≫ pointedMappingComposition X Y Z) ≫
        (PointedObject.basedHomMap X b).right := by
  rw [← tensorHom_comp_whiskerLeft, Category.assoc, ← pointedMappingComposition_post,
    ← Category.assoc]

/-- 合成族の前合成を第一の因子へ移せる。 -/
lemma pointedMappingComposition_families_pre {P Q : SSet.{u}}
    {X X' Y Z : PointedSimplicialSet.{u}}
    (f : P ⟶ (PointedObject.basedHom X Y).right)
    (g : Q ⟶ (PointedObject.basedHom Y Z).right) (a : X' ⟶ X) :
    ((f ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Y).right) ⊗ₘ g) ≫ pointedMappingComposition X' Y Z =
      ((f ⊗ₘ g) ≫ pointedMappingComposition X Y Z) ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed a Z).right := by
  rw [← tensorHom_comp_whiskerRight, Category.assoc, ← pointedMappingComposition_pre,
    ← Category.assoc]

end SerrePositivity.KST.SConstruction
