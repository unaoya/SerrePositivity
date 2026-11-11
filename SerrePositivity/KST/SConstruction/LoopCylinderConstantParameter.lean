module
public import SerrePositivity.KST.SConstruction.LoopOfCylinder

/-! # 定数な区間族のパラメータ上の loop の固定
概要：区間全体で基点に写るパラメータ部分は、円への降下と curry の後も定数 loop に写る。
方針：元の cofiber cylinder の二脚で降下後の定数性を検出し、指数の包含後で curry を比較する。
規約：パラメータ写像は任意。使われ方：零段の退化像から点つき零行を作る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

/-- 区間全体で基点に写るパラメータ部分は、円への降下後も厳密に基点に定数。 -/
lemma circleCylinderDesc_constant_parameter {A P : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right) (h₀ h₁) (a : P ⟶ A)
    (ha : (a ▷ (Δ[1] : SSet.{u})) ≫ h = toUnit (P ⊗ (Δ[1] : SSet.{u})) ≫ B.hom) :
    (PointedSimplicialSet.circle.{u}.right ◁ a) ≫ circleCylinderDesc B h h₀ h₁ =
      toUnit (PointedSimplicialSet.circle.{u}.right ⊗ P) ≫ B.hom := by
  let q : (Δ[1] : SSet.{u}) ⟶ PointedSimplicialSet.circle.{u}.right :=
    PointedObject.cofiberQuotient (boundary.{u} 1).ι
  have hq : (q ▷ A) ≫ circleCylinderDesc B h h₀ h₁ =
      (β_ (Δ[1] : SSet.{u}) A).hom ≫ h := circleCylinderDesc_quotient B h h₀ h₁
  apply rawCofiberCylinder_hom_ext (boundary.{u} 1).ι P
  · change (q ▷ P) ≫ (PointedSimplicialSet.circle.{u}.right ◁ a) ≫
      circleCylinderDesc B h h₀ h₁ = (q ▷ P) ≫
        toUnit (PointedSimplicialSet.circle.{u}.right ⊗ P) ≫ B.hom
    rw [← Category.assoc, ← whisker_exchange, Category.assoc, hq,
      ← Category.assoc, BraidedCategory.braiding_naturality_right, Category.assoc, ha]
    simp only [comp_toUnit_assoc]
  · change (PointedSimplicialSet.circle.{u}.hom ▷ P) ≫
      (PointedSimplicialSet.circle.{u}.right ◁ a) ≫ circleCylinderDesc B h h₀ h₁ =
      (PointedSimplicialSet.circle.{u}.hom ▷ P) ≫
        toUnit (PointedSimplicialSet.circle.{u}.right ⊗ P) ≫ B.hom
    rw [← Category.assoc, ← whisker_exchange, Category.assoc, circleCylinderDesc_point]
    simp only [comp_toUnit_assoc]

/-- 区間全体で基点に写るパラメータ部分は、構成した loop 射でも定数 loop に写る。 -/
lemma loopOfCylinder_constant_parameter {A P : SSet.{u}} (B : PointedSimplicialSet.{u})
    (h : A ⊗ (Δ[1] : SSet.{u}) ⟶ B.right) (h₀ h₁) (a : P ⟶ A)
    (ha : (a ▷ (Δ[1] : SSet.{u})) ≫ h = toUnit (P ⊗ (Δ[1] : SSet.{u})) ≫ B.hom) :
    a ≫ loopOfCylinder B h h₀ h₁ = toUnit P ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace B).hom := by
  apply (cancel_mono (PointedObject.basedHomι PointedSimplicialSet.circle.{u} B)).mp
  rw [Category.assoc]
  change a ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry PointedSimplicialSet.circle.{u} B
    (circleCylinderDesc B h h₀ h₁) _ ≫ _) = _
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, ← MonoidalClosed.curry_natural_left,
    circleCylinderDesc_constant_parameter B h h₀ h₁ a ha, PointedObject.curry_constant,
    Category.assoc, PointedObject.basedHom_basepoint_ι]
  rfl

end SerrePositivity.KST.SConstruction
