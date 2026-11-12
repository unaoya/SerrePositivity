module

public import SerrePositivity.KST.LocalizingInvariants.FunctorHomWhiskering
public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：端点輸送を含む Arrow の等号は、射の合成と整合する。
方針：Arrow の等号を端点と射の等号へ分解し、等号の輸送を消去する。
規約：点ごとの比較ではない。使われ方：cofiber の指定右辺の全関手比較。
-/

@[expose] public section
universe u v
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {B : Type u} [Category.{v} B]

lemma arrow_mk_eqToHom_comp {x x' y : B}
    (h : x' = x) (f : x ⟶ y) : Arrow.mk (eqToHom h ≫ f) = Arrow.mk f := by
  cases h
  simp only [eqToHom_refl, Category.id_comp]

lemma arrow_mk_comp_eqToHom {x y y' : B}
    (f : x ⟶ y) (h : y = y') : Arrow.mk (f ≫ eqToHom h) = Arrow.mk f := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

lemma arrow_mk_comp_congr {a b c a' b' c' : B}
    {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'} {g' : b' ⟶ c'}
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hf
  cases ha
  cases hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  subst f'
  obtain ⟨_, hc, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  cases hc
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg
  subst g'
  rfl

lemma arrow_mk_comp_of_identity {a b c : B} (f : a ⟶ b) (g : b ⟶ c)
    (h : Arrow.mk f = Arrow.mk (𝟙 b)) : Arrow.mk (f ≫ g) = Arrow.mk g := by
  have he := arrow_mk_comp_congr h (rfl : Arrow.mk g = Arrow.mk g)
  simpa only [Category.id_comp] using he

lemma hom_eq_of_arrow_mk_eq {a b : B} {f g : a ⟶ b}
    (h : Arrow.mk f = Arrow.mk g) : f = g := by
  obtain ⟨_, _, he⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using he

lemma homPre_arrow_congr {A B X : SSet.{u}} (i : A ⟶ B)
    {F G F' G' : B ⟶ X} {α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G} {β : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F' G'}
    (h : Arrow.mk α = Arrow.mk β) : Arrow.mk (homPre i α) = Arrow.mk (homPre i β) :=
  congrArg (hoFunctor.map ((pre i).app X)).toFunctor.mapArrow.obj h

end SerrePositivity.KST.LocalizingInvariants
