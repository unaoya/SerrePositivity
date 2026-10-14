module

public import SerrePositivity.CategoryTheory.Monoidal.ModuleClosed
public import SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomFree
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorFreeLeft

/-! # 左自由因子との比較の下での逆転置と通常の評価 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalModuleInternalHom

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [SymmetricCategory C] (M : C) [MonObj M] [IsCommMonObj M]
  [HasEqualizers C] [HasCoequalizers C]
  [∀ Z : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]

/-- 左自由因子の比較の逆射と逆転置の合成は、比較した通常の内部Homの評価。 -/
lemma freeLeftIso_uncurry (X : C) {A F : Mod C M}
    (f : A ⟶ moduleObj M (MonoidalFreeModule.freeObj M X) F) :
    (MonoidalBalancedTensor.freeLeftIso M X A).inv.hom ≫
        (uncurryModule M (MonoidalFreeModule.freeObj M X) f).hom =
      X ◁ (f.hom ≫ (freeHomIso M X F).hom) ≫ (ihom.ev X).app F.X := by
  rw [MonoidalBalancedTensor.freeLeftIso_inv]
  rw [Category.assoc, projection_uncurryModule]
  rw [← whisker_exchange_assoc]
  erw [← freeHomIso_evaluation]
  rw [← whiskerLeft_comp_assoc]

end SerrePositivity.MonoidalModuleInternalHom
