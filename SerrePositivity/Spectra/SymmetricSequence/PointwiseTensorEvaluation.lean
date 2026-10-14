module

public import SerrePositivity.Spectra.SymmetricSequence.PointwiseTensorModule

/-! # 各段の通常のテンソル積の評価と転置の法則 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.SymmetricSequence

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.Limits
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [HasColimitsOfSize.{0, 0} C] [HasLimitsOfSize.{0, 0} C]
  [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
  (M : SymmetricSequence C) [MonObj M] [IsCommMonObj M]

/-- 各段の通常のテンソル積からの評価が内部Homの評価になるという法則。 -/
def pointwiseTensorEvaluationLevelLaw (X : C) {A F : Mod (SymmetricSequence C) M}
    (a : A.X ≅ unshiftedInternalHom X F.X) (q : ℕ)
    (h : pointwiseTensorModule M X A ⟶ F) : Prop :=
  h.hom.app (FiniteBijection.of q) =
    X ◁ a.hom.app (FiniteBijection.of q) ≫ (ihom.ev X).app (level F.X q)

omit [HasEqualizers (SymmetricSequence C)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)] in
/-- 自由零生成加群の各段の評価法則を全体の逆比較で移す。 -/
lemma pointwiseTensorEvaluationLevelLaw_of_freeZero (X : C)
    {A F : Mod (SymmetricSequence C) M} (a : A.X ≅ unshiftedInternalHom X F.X) (q : ℕ)
    (g : MonoidalBalancedTensor.moduleObj M
      (MonoidalFreeModule.freeObj M ((freeAt 0).obj X)) A ⟶ F)
    (h : pointwiseTensorModule M X A ⟶ F)
    (hh : h = (freeZeroTensorPointwiseModuleIso M X A).inv ≫ g)
    (hg : freeZeroModuleEvaluationLevelLaw M X a q g) :
    pointwiseTensorEvaluationLevelLaw M X a q h := by
  unfold pointwiseTensorEvaluationLevelLaw
  rw [hh]
  change (freeZeroTensorPointwiseModuleIso M X A).inv.hom.app (FiniteBijection.of q) ≫
    g.hom.app (FiniteBijection.of q) = _
  have hi := congrArg Iso.inv (freeZeroTensorPointwiseModuleIso_level M X A q)
  change (freeZeroTensorPointwiseModuleIso M X A).inv.hom.app (FiniteBijection.of q) =
    (freeZeroTensorModuleLevelIso M X A q).inv at hi
  rw [hi]
  exact hg

/-- 各段の逆転置が通常の内部Homの逆転置になるという法則。 -/
def pointwiseTensorUncurryLevelLaw (X : C) {A B F : Mod (SymmetricSequence C) M}
    (a : B.X ≅ unshiftedInternalHom X F.X) (f : A ⟶ B)
    (h : pointwiseTensorModule M X A ⟶ F) (q : ℕ) : Prop :=
  h.hom.app (FiniteBijection.of q) =
    uncurry (f.hom.app (FiniteBijection.of q) ≫ a.hom.app (FiniteBijection.of q))

omit [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
  [IsCommMonObj M] in
/-- 関手の射の公式と評価法則から、各段の通常の逆転置を得る。 -/
lemma pointwiseTensorUncurryLevelLaw_of_evaluation (X : C)
    {A B F : Mod (SymmetricSequence C) M} (a : B.X ≅ unshiftedInternalHom X F.X)
    (f : A ⟶ B) (h : pointwiseTensorModule M X A ⟶ F)
    (e : pointwiseTensorModule M X B ⟶ F) (q : ℕ)
    (hh : h = (pointwiseTensorModuleFunctor M X).map f ≫ e)
    (he : pointwiseTensorEvaluationLevelLaw M X a q e) :
    pointwiseTensorUncurryLevelLaw M X a f h q := by
  unfold pointwiseTensorUncurryLevelLaw
  rw [hh, uncurry_eq]
  change ((pointwiseTensorModuleFunctor M X).map f).hom.app (FiniteBijection.of q) ≫
    e.hom.app (FiniteBijection.of q) = _
  rw [pointwiseTensorModuleFunctor_map_app]
  erw [he, whiskerLeft_comp, Category.assoc]
  rfl

/-- 各段の転置が通常の内部Homの転置になるという法則。 -/
def pointwiseTensorCurryLevelLaw (X : C) {A B F : Mod (SymmetricSequence C) M}
    (a : B.X ≅ unshiftedInternalHom X F.X) (g : pointwiseTensorModule M X A ⟶ F)
    (f : A ⟶ B) (q : ℕ) : Prop :=
  f.hom.app (FiniteBijection.of q) ≫ a.hom.app (FiniteBijection.of q) =
    curry (g.hom.app (FiniteBijection.of q))

omit [HasEqualizers (SymmetricSequence C)] [HasCoequalizers (SymmetricSequence C)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
  [∀ Z : SymmetricSequence C, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
  [IsCommMonObj M] in
/-- 通常の逆転置の法則から、各段の通常の転置の法則を得る。 -/
lemma pointwiseTensorCurryLevelLaw_of_uncurry (X : C)
    {A B F : Mod (SymmetricSequence C) M} (a : B.X ≅ unshiftedInternalHom X F.X)
    (g : pointwiseTensorModule M X A ⟶ F) (f : A ⟶ B) (q : ℕ)
    (hg : pointwiseTensorUncurryLevelLaw M X a f g q) :
    pointwiseTensorCurryLevelLaw M X a g f q := by
  exact (eq_curry_iff _ _).mpr hg.symm

end SerrePositivity.SymmetricSequence
