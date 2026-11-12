module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ArrowFamilyHomNaturality

public import SerrePositivity.KST.LocalizingInvariants.ArrowFamilyHomotopy
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomExchange

/-!
概要：矢印全族が表す自然変換は、パラメータ制限と図式比較に自然。
方針：元の prism の前合成を照合し、関手圏内の交換則を適用する。
規約：各点での可換性に弱めない。使われ方：cofiber の全図式比較の指定右辺。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma arrowFamilyHom_precomp {A B X : SSet.{u}}
    (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (i : B ⟶ A) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom (i ≫ a) = homPre i (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom a) := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom homPre
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom]
  congr 1

lemma arrowFamilyHom_postcomp {A X Y : SSet.{u}}
    (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (F : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom (a ≫ (ihom (Δ[1] : SSet.{u})).map F) =
      homPost F (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom a) := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom homPost
  rw [← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom]
  congr 1

lemma arrowFamilyHom_naturality {A X : SSet.{u}}
    [Quasicategory A] [Quasicategory X]
    (f g : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom f g) :
    homPost (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) α ≫
        _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom g =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom f ≫
        homPost (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) α := by
  have h := homPost_homPre_exchange α
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.arrowFamilyHom (𝟙 ((ihom (Δ[1] : SSet.{u})).obj X)))
  rw [← arrowFamilyHom_precomp, ← arrowFamilyHom_precomp] at h
  exact h

end SerrePositivity.KST.LocalizingInvariants
