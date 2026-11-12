module

public import SerrePositivity.KST.LocalizingInvariants.ZeroArrowFamily
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：矢印族と代表ホモトピーの往復およびパラメータ制限の整合。
方針：curry の逆則と二回の座標交換を使う。
規約：raw な射の厳密等式。使われ方：lax pullback の単位の時間端点の回収。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.ZeroArrowFamily
variable {A B X : SSet.{u}} {f g : A ⟶ X}

lemma ofHomotopy_eq_of_h (H : SSet.Homotopy f g)
    (e : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (he : H.h = (β_ A (Δ[1] : SSet.{u})).hom ≫ uncurry e) : ofHomotopy H = e := by
  rw [ofHomotopy, he, ← Category.assoc, SymmetricCategory.symmetry, Category.id_comp,
    curry_uncurry]

lemma ofHomotopy_precomp (H : SSet.Homotopy f g) (i : B ⟶ A) :
    ofHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H i) = i ≫ ofHomotopy H := by
  apply uncurry_injective
  rw [ofHomotopy, uncurry_curry, uncurry_natural_left, ofHomotopy, uncurry_curry]
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨z, b⟩
  rfl

lemma ofHomotopy_postcomp {Y : SSet.{u}} (H : SSet.Homotopy f g) (r : X ⟶ Y) :
    ofHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H r) =
      ofHomotopy H ≫ (ihom (Δ[1] : SSet.{u})).map r := by
  apply uncurry_injective
  rw [ofHomotopy, uncurry_curry, uncurry_natural_right, ofHomotopy, uncurry_curry]
  rfl

end SerrePositivity.KST.LocalizingInvariants.ZeroArrowFamily
