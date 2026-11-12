module
public import SerrePositivity.KST.Spectra.PointedEnrichment
public import SerrePositivity.KST.Spectra.PointedHomotopyClasses

/-! # 元の点つき射を定数族として合成する式
概要：豊穣合成の一方を元の点つき射の定数族にすると通常の前後合成を回収する。
方針：定数族を単位対象への射で表示し、豊穣の前後合成の定義を計算する。
規約：全パラメータの実写像の等式であり、成分への移行を使わない。
使われ方：K の二本の補正列を合成の同じ中間族で連結する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra Spectra.PointedMapping
local instance pointedConstantCompositionSimplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 定数な元の射の族は、単位への射と同じ豊穣通常射の合成である。 -/
lemma pointedFamilyConstant_eq {U : SSet.{u}} {A B : PointedSimplicialSet.{u}}
    (f : A ⟶ B) :
    SSet.const (X := U) (familyVertex f) = toUnit U ≫ eHomEquiv SSet f := by
  rw [familyVertex_eq_pointedHomVertex]
  have h : eHomEquiv SSet f =
      (SSet.unitHomEquiv _).symm (pointedHomVertexEquiv A B f) := by
    apply (SSet.unitHomEquiv _).injective
    exact (Equiv.apply_symm_apply _ _).symm
  rw [h]
  rfl

/-- 右側が定数な元の射なら、全族の豊穣合成は通常の後合成となる。 -/
lemma pointedFamilyComposition_const_right {U : SSet.{u}} {A B C : PointedSimplicialSet.{u}}
    (a : U ⟶ (PointedObject.basedHom A B).right) (g : B ⟶ C) :
    lift a (SSet.const (familyVertex g)) ≫ eComp SSet A B C =
      a ≫ (PointedObject.basedHomMap A g).right := by
  rw [pointedFamilyConstant_eq, ← PointedEnrichment.whiskerLeft_eq]
  dsimp only [eHomWhiskerLeft]
  simp only [← Category.assoc]
  congr 1

/-- 左側が定数な元の射なら、全族の豊穣合成は通常の前合成となる。 -/
lemma pointedFamilyComposition_const_left {U : SSet.{u}} {A B C : PointedSimplicialSet.{u}}
    (f : A ⟶ B) (b : U ⟶ (PointedObject.basedHom B C).right) :
    lift (SSet.const (familyVertex f)) b ≫ eComp SSet A B C =
      b ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre f C := by
  rw [pointedFamilyConstant_eq, ← PointedEnrichment.whiskerRight_eq]
  dsimp only [eHomWhiskerRight]
  simp only [← Category.assoc]
  congr 1

end SerrePositivity.KST.SConstruction
