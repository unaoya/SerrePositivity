module


public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.InternalHomFlipAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
概要：余積・pushout 上の関手族を、元の制限を厳密に保って貼り合わせる。
方針：反変内部 Hom の自己随伴で、通常の余極限の貼合せへ移す。
規約：全パラメータ・充填性の仮定なし。使われ方：一般商の可逆区間の一斉付加。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open _root_.SerrePositivity.KST.LocalizingInvariants

def coproductFamilyGlue {I : Type u} {K : I → SSet.{u}} {B X : SSet.{u}}
    (f : ∀ i, B ⟶ (ihom (K i)).obj X) : B ⟶ (ihom (∐ K)).obj X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B (∐ K) X).symm
    (Sigma.desc (fun i => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B (K i) X (f i)))

lemma coproductFamilyGlue_restrict {I : Type u} {K : I → SSet.{u}} {B X : SSet.{u}}
    (f : ∀ i, B ⟶ (ihom (K i)).obj X) (i : I) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coproductFamilyGlue f ≫ (pre (Sigma.ι K i)).app X = f i := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B (K i) X).injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.coproductFamilyGlue, Equiv.apply_symm_apply, Sigma.ι_comp_desc]

lemma coproductFamily_hom_ext {I : Type u} {K : I → SSet.{u}} {B X : SSet.{u}}
    {f g : B ⟶ (ihom (∐ K)).obj X}
    (h : ∀ i, f ≫ (pre (Sigma.ι K i)).app X = g ≫ (pre (Sigma.ι K i)).app X) : f = g := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B (∐ K) X).injective
  apply Sigma.hom_ext
  intro i
  have hi := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B (K i) X) (h i)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app] using hi

def pushoutFamilyGlue {A C D B X : SSet.{u}} (i : A ⟶ C) (j : A ⟶ D)
    (f : B ⟶ (ihom C).obj X) (g : B ⟶ (ihom D).obj X)
    (h : f ≫ (pre i).app X = g ≫ (pre j).app X) :
    B ⟶ (ihom (pushout i j)).obj X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B (pushout i j) X).symm (pushout.desc
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B C X f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B D X g) (by
      have ht := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B A X) h
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app] using ht))

lemma pushoutFamilyGlue_inl {A C D B X : SSet.{u}} (i : A ⟶ C) (j : A ⟶ D)
    (f : B ⟶ (ihom C).obj X) (g : B ⟶ (ihom D).obj X)
    (h : f ≫ (pre i).app X = g ≫ (pre j).app X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFamilyGlue i j f g h ≫ (pre (pushout.inl i j)).app X = f := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B C X).injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFamilyGlue, Equiv.apply_symm_apply, pushout.inl_desc]

lemma pushoutFamilyGlue_inr {A C D B X : SSet.{u}} (i : A ⟶ C) (j : A ⟶ D)
    (f : B ⟶ (ihom C).obj X) (g : B ⟶ (ihom D).obj X)
    (h : f ≫ (pre i).app X = g ≫ (pre j).app X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFamilyGlue i j f g h ≫ (pre (pushout.inr i j)).app X = g := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B D X).injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pushoutFamilyGlue, Equiv.apply_symm_apply, pushout.inr_desc]

lemma pushoutFamily_hom_ext {A C D B X : SSet.{u}} (i : A ⟶ C) (j : A ⟶ D)
    {f g : B ⟶ (ihom (pushout i j)).obj X}
    (h : f ≫ (pre (pushout.inl i j)).app X = g ≫ (pre (pushout.inl i j)).app X)
    (k : f ≫ (pre (pushout.inr i j)).app X = g ≫ (pre (pushout.inr i j)).app X) : f = g := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B (pushout i j) X).injective
  apply pushout.hom_ext
  · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app] using
      congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B C X) h
  · simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app] using
      congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv B D X) k

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
