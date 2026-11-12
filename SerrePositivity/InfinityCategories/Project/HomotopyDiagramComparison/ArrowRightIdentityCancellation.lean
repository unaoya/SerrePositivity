module

public import Mathlib.CategoryTheory.Comma.Arrow

/-!
概要：異なる端点表示を含む恒等因子を、合成の Arrow の等式から消去する。
方針：型付き端点を等式で揃え、通常の右単位則を適用する。
規約：因子の同じ射の類を要求。使われ方：底で恒等な比較を元の HL・HR の類から消す。
-/

@[expose] public section
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 合成が h であり最後の因子が恒等なら、最初の因子と h は同じ Arrow である。 -/
lemma arrowRightIdentity_cancel {C : Type*} [Category* C] {a b c w : C}
    (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) (hfg : f ≫ g = h)
    (hg : Arrow.mk g = Arrow.mk (𝟙 w)) : Arrow.mk f = Arrow.mk h := by
  obtain ⟨hb, hc, hg⟩ := (Arrow.mk_eq_mk_iff _ _).mp hg
  subst w c
  simp only [eqToHom_refl, Category.comp_id] at hg
  rw [hg, Category.comp_id] at hfg
  exact congrArg Arrow.mk hfg

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
