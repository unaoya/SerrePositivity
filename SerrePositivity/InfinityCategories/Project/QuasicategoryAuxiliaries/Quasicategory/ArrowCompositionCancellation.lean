module

public import Mathlib.CategoryTheory.Comma.Arrow


/-!
概要：端点も含む Arrow の等号から、可逆な左因子を相殺する。
方針：端点と射の等号に分解し、元の圏の epi 消去を使う。
規約：端点輸送も消去に含める。使われ方：実積同値による辺の照合。
-/

@[expose] public section
universe u v
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory
open _root_.SerrePositivity.KST.LocalizingInvariants
variable {B : Type u} [Category.{v} B]

lemma arrow_mk_comp_of_any_identity {a b c d : B} (f : a ⟶ b) (g : b ⟶ c)
    (h : Arrow.mk f = Arrow.mk (𝟙 d)) : Arrow.mk (f ≫ g) = Arrow.mk g := by
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp h
  cases ha
  cases hb
  simp only [eqToHom_refl, Category.comp_id] at hf
  rw [hf, Category.id_comp]

lemma arrow_mk_cancel_comp_left {a b c a' b' c' : B}
    {f : a ⟶ b} {g : b ⟶ c} {f' : a' ⟶ b'} {g' : b' ⟶ c'} [IsIso f']
    (hf : Arrow.mk f = Arrow.mk f') (hfg : Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g')) :
    Arrow.mk g = Arrow.mk g' := by
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hf
  cases ha
  cases hb
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf
  subst f'
  obtain ⟨_, hc, hfg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hfg
  cases hc
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hfg
  exact congrArg Arrow.mk ((cancel_epi f).mp hfg)

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
