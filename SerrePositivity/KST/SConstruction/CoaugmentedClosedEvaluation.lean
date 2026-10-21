module
public import SerrePositivity.KST.SConstruction.CoaugmentedClosedFamily

/-! # 元の全族に対する monoidal な単位の自然性
概要：全 Hom 作用への単位は、元の同じ全パラメータ作用と厳密に可換する。
方針：monoidal な単位の tensor 式と、元の評価に関する自然性を使う。
規約：全入力を保持する。使われ方：点つき Ex∞ の基点保存と元の模型との比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open Functor.LaxMonoidal
variable (F : SSet.{u} ⥤ SSet.{u}) [F.LaxMonoidal]
  (η : 𝟭 SSet.{u} ⟶ F) [NatTrans.IsMonoidal η]

/-- 元の評価の全単体は、同じ monoidal な単位の像で厳密に回収される。 -/
lemma coaugmentedClosedFamilyMap_evaluation (X Y : SSet.{u}) :
    (η.app X ▷ (ihom X).obj Y) ≫ uncurry (coaugmentedClosedFamilyMap F η X Y) =
      (ihom.ev X).app Y ≫ η.app Y := by
  have ht := NatTrans.IsMonoidal.tensor (τ := η) X ((ihom X).obj Y)
  change 𝟙 _ ≫ η.app (X ⊗ (ihom X).obj Y) = _ at ht
  rw [Category.id_comp] at ht
  rw [coaugmentedClosedFamilyMap, uncurry_natural_left,
    laxClosedFamilyMap, uncurry_curry, ← Category.assoc, ← tensorHom_def,
    ← Category.assoc, ← ht]
  exact (η.naturality ((ihom.ev X).app Y)).symm

/-- 任意の全入力族の作用は、同じ単位に沿って元の全族を厳密に回収する。 -/
lemma coaugmentedClosedFamilyMap_action {X Y P : SSet.{u}}
    (a : P ⟶ (ihom X).obj Y) :
    (η.app X ▷ P) ≫ uncurry (a ≫ coaugmentedClosedFamilyMap F η X Y) =
      uncurry a ≫ η.app Y := by
  rw [uncurry_natural_left, ← Category.assoc, ← whisker_exchange, Category.assoc,
    coaugmentedClosedFamilyMap_evaluation, ← Category.assoc]
  exact congrArg (fun q => q ≫ η.app Y) (uncurry_eq a).symm

end SerrePositivity.KST.SConstruction
