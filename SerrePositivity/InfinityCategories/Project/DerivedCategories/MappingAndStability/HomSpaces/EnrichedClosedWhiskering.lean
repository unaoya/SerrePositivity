module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.EnrichedIdentityWhiskering
/-!
概要：閉射による豊穣前合成を元の合成閉射へ同定する。
方針：実二射影と mapping cocone の持ち上げを使う。
規約：分解変更比較の同定は別工程。使われ方：模型変更の全自然性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory
lemma enrichedClosed_precompose (V : Type u) [Category.{v} V] [MonoidalCategory V]
    (C : Type w) [Category.{z} C] [EnrichedOrdinaryCategory V C]
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V g ≫ eHomWhiskerRight V f Z = eHomEquiv V (f ≫ g) := by
  rw [eHomEquiv_comp]
  dsimp only [eHomWhiskerRight]
  rw [leftUnitor_inv_naturality_assoc]
  simp only [tensorHom_def', Category.assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
