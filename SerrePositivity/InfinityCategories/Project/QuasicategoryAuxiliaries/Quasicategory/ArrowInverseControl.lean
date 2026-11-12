module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.ArrowCompositionCancellation

/-!
概要：端点を含む Arrow の等号による右因子の消去と逆射の比較。
方針：端点の等号を消去した後、通常の mono 消去と逆射の一意性を使う。
規約：可逆性は消去する実射に要求。使われ方：fiber の置換比較の頂点を元の BF 射へ戻す。
-/

@[expose] public section
universe u v
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants
variable {B : Type u} [Category.{v} B]

lemma arrow_mk_cancel_comp_right {a b c a' b' c' : B}
    {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'} {g' : b' ⟶ c'} [IsIso g']
    (hg : Arrow.mk g = Arrow.mk g') (hfg : Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g')) :
    Arrow.mk f = Arrow.mk f' := by
  obtain ⟨hb, hc, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  cases hb
  cases hc
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hg
  subst g'
  obtain ⟨ha, _, hfg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hfg
  cases ha
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hfg
  exact congrArg Arrow.mk ((cancel_mono g).mp hfg)

lemma arrow_mk_inv_congr {a b a' b' : B} {f : a ⟶ b} {g : a' ⟶ b'} [IsIso f] [IsIso g]
    (h : Arrow.mk f = Arrow.mk g) : Arrow.mk (inv f) = Arrow.mk (inv g) := by
  obtain ⟨ha, hb, h⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  cases ha
  cases hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
  subst g
  rfl

lemma arrow_mk_comp_right_of_any_identity {a b c d : B} (f : a ⟶ b) (g : b ⟶ c)
    (h : Arrow.mk g = Arrow.mk (𝟙 d)) : Arrow.mk (f ≫ g) = Arrow.mk f := by
  obtain ⟨hb, hc, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  cases hb
  cases hc
  simp only [eqToHom_refl, Category.comp_id] at hg
  rw [hg, Category.comp_id]

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrow_mk_cancel_comp_right := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_cancel_comp_right

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrow_mk_comp_right_of_any_identity := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_comp_right_of_any_identity

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.arrow_mk_inv_congr := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.arrow_mk_inv_congr
