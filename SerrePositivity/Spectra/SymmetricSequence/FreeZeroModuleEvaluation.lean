module

public import SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomFreeLeftEvaluation
public import SerrePositivity.CategoryTheory.Monoidal.ModuleInternalHomTransport
public import SerrePositivity.Spectra.SymmetricSequence.FreeZeroConvolution

/-! # 生成次数零の係数加群のcotensorと各段の評価 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]

variable (M : SymmetricSequence C) [MonObj M] [IsCommMonObj M]

/-- 生成次数零の比較で作用を移した、各段の通常の内部Homを持つ係数加群。 -/
def freeZeroCotensorModule (X : C) (F : Mod (SymmetricSequence C) M)
    (e : (ihom ((freeAt 0).obj X)).obj F.X ≅ unshiftedInternalHom X F.X) :=
  MonoidalModuleInternalHom.transportedObj M ((freeAt 0).obj X) F e

/-- 自由原変数の内部Homと各段の通常の内部Homの係数加群としての比較。 -/
def freeZeroCotensorModuleIso (X : C) (F : Mod (SymmetricSequence C) M)
    (e : (ihom ((freeAt 0).obj X)).obj F.X ≅ unshiftedInternalHom X F.X) :=
  MonoidalModuleInternalHom.freeHomModuleIso M ((freeAt 0).obj X) F ≪≫
    MonoidalModuleInternalHom.transportedIso M ((freeAt 0).obj X) F
      e

/-- 係数加群としての比較の逆射を逆転置した評価。 -/
def freeZeroCotensorModuleEvaluation (X : C) (F : Mod (SymmetricSequence C) M)
    (e : (ihom ((freeAt 0).obj X)).obj F.X ≅ unshiftedInternalHom X F.X) :=
  MonoidalModuleInternalHom.uncurryModule M
    (MonoidalFreeModule.freeObj M ((freeAt 0).obj X)) (freeZeroCotensorModuleIso M X F e).inv

/-- 自由零生成加群とのテンソル積の各段を通常のテンソル積へ比較する。 -/
def freeZeroTensorModuleLevelIso (X : C) (A : Mod (SymmetricSequence C) M) (q : ℕ) :
    level (MonoidalBalancedTensor.moduleObj M
      (MonoidalFreeModule.freeObj M ((freeAt 0).obj X)) A).X q ≅ X ⊗ level A.X q :=
  ((Mod.forget (D := SymmetricSequence C) M) ⋙ evaluation q).mapIso
      (MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj X) A) ≪≫
    freeZeroConvolutionLevelIso X A.X q

/-- 左自由因子の比較の下で、係数加群の評価は移送後の通常の評価。 -/
lemma freeZeroCotensorModuleEvaluation_freeLeft (X : C) (F : Mod (SymmetricSequence C) M)
    (e : (ihom ((freeAt 0).obj X)).obj F.X ≅ unshiftedInternalHom X F.X) :
    (MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj X)
        (freeZeroCotensorModule M X F e)).inv.hom ≫
      (freeZeroCotensorModuleEvaluation M X F e).hom =
    (freeAt 0).obj X ◁ e.inv ≫
      (ihom.ev ((freeAt 0).obj X)).app F.X := by
  unfold freeZeroCotensorModuleEvaluation
  rw [MonoidalModuleInternalHom.freeLeftIso_uncurry]
  change (freeAt 0).obj X ◁
    ((e.inv ≫
      (MonoidalModuleInternalHom.freeHomIso M ((freeAt 0).obj X) F).inv) ≫
      (MonoidalModuleInternalHom.freeHomIso M ((freeAt 0).obj X) F).hom) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- 各段の逆比較を介した係数加群の評価は、基礎圏の通常の内部Homの評価。 -/
lemma freeZeroCotensorModuleEvaluation_level (X : C) (F : Mod (SymmetricSequence C) M)
    (e : (ihom ((freeAt 0).obj X)).obj F.X ≅ unshiftedInternalHom X F.X)
    (q : ℕ) (he : e.inv = (freeZeroInternalHomNatIso X).inv.app F.X) :
    (freeZeroTensorModuleLevelIso M X (freeZeroCotensorModule M X F e) q).inv ≫
        (freeZeroCotensorModuleEvaluation M X F e).hom.app (FiniteBijection.of q) =
      (ihom.ev X).app (level F.X q) := by
  have h := congrArg (fun k => k.app (FiniteBijection.of q))
    (freeZeroCotensorModuleEvaluation_freeLeft M X F e)
  change ((freeZeroConvolutionLevelIso X (freeZeroCotensorModule M X F e).X q).inv ≫
    (MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj X)
        (freeZeroCotensorModule M X F e)).inv.hom.app (FiniteBijection.of q)) ≫
      (freeZeroCotensorModuleEvaluation M X F e).hom.app (FiniteBijection.of q) = _
  rw [Category.assoc, ← NatTrans.comp_app, h, he]
  exact freeZeroConvolutionLevelIso_inv_evaluation X F.X q

/-- 自由零生成加群からの逆転置を、各段の通常の内部Homの評価で計算する。 -/
lemma freeZeroUncurryModule_level (X : C) {A F : Mod (SymmetricSequence C) M}
    (f : A ⟶ MonoidalModuleInternalHom.moduleObj M
      (MonoidalFreeModule.freeObj M ((freeAt 0).obj X)) F)
    (a : A.X ≅ unshiftedInternalHom X F.X) (q : ℕ)
    (hf : f.hom ≫ (MonoidalModuleInternalHom.freeHomIso M ((freeAt 0).obj X) F).hom =
      a.hom ≫ (freeZeroInternalHomNatIso X).inv.app F.X) :
    (freeZeroTensorModuleLevelIso M X A q).inv ≫
        (MonoidalModuleInternalHom.uncurryModule M
          (MonoidalFreeModule.freeObj M ((freeAt 0).obj X)) f).hom.app (FiniteBijection.of q) =
      X ◁ a.hom.app (FiniteBijection.of q) ≫ (ihom.ev X).app (level F.X q) := by
  have h := congrArg (fun k => k.app (FiniteBijection.of q))
    (MonoidalModuleInternalHom.freeLeftIso_uncurry M ((freeAt 0).obj X) f)
  rw [hf] at h
  change ((freeZeroConvolutionLevelIso X A.X q).inv ≫
    (MonoidalBalancedTensor.freeLeftIso M ((freeAt 0).obj X) A).inv.hom.app
      (FiniteBijection.of q)) ≫ _ = _
  rw [Category.assoc, ← NatTrans.comp_app, h]
  apply (cancel_epi (freeZeroConvolutionLevelIso X A.X q).hom).mp
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hn := congrArg (fun k => k.app (FiniteBijection.of q))
    ((freeZeroConvolutionNatIso X).hom.naturality a.hom)
  change ((freeAt 0).obj X ◁ a.hom).app (FiniteBijection.of q) ≫
      (freeZeroConvolutionLevelIso X (unshiftedInternalHom X F.X) q).hom =
    (freeZeroConvolutionLevelIso X A.X q).hom ≫ X ◁ a.hom.app (FiniteBijection.of q) at hn
  erw [← hn, Category.assoc, freeZeroConvolutionLevelIso_evaluation]
  simp only [whiskerLeft_comp, Category.assoc]
  rfl

/-- 各段の逆比較の下で、与えた加群射が通常の内部Homの評価になるという法則。 -/
def freeZeroModuleEvaluationLevelLaw (X : C) {A F : Mod (SymmetricSequence C) M}
    (a : A.X ≅ unshiftedInternalHom X F.X) (q : ℕ)
    (g : MonoidalBalancedTensor.moduleObj M
      (MonoidalFreeModule.freeObj M ((freeAt 0).obj X)) A ⟶ F) : Prop :=
  (freeZeroTensorModuleLevelIso M X A q).inv ≫ g.hom.app (FiniteBijection.of q) =
    X ◁ a.hom.app (FiniteBijection.of q) ≫ (ihom.ev X).app (level F.X q)

/-- 逆転置の各段の評価法則を、係数加群の比較と評価の条件から得る。 -/
lemma freeZeroUncurryModule_levelLaw (X : C) {A F : Mod (SymmetricSequence C) M}
    (f : A ⟶ MonoidalModuleInternalHom.moduleObj M
      (MonoidalFreeModule.freeObj M ((freeAt 0).obj X)) F)
    (a : A.X ≅ unshiftedInternalHom X F.X) (q : ℕ)
    (hf : f.hom ≫ (MonoidalModuleInternalHom.freeHomIso M ((freeAt 0).obj X) F).hom =
      a.hom ≫ (freeZeroInternalHomNatIso X).inv.app F.X) :
    freeZeroModuleEvaluationLevelLaw M X a q
      (MonoidalModuleInternalHom.uncurryModule M
        (MonoidalFreeModule.freeObj M ((freeAt 0).obj X)) f) :=
  freeZeroUncurryModule_level M X f a q hf

end SerrePositivity.SymmetricSequence
