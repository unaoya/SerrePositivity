module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArrowRightIdentityCancellation

/-!
概要：異なる端点表示を含む左の恒等因子を、合成の Arrow の等式から消去する。
方針：型付き端点を等式で揃え、通常の左単位則を適用する。
規約：同じ射の類を要求。使われ方：動く終端を持つ切断比較の自然性。
-/

@[expose] public section
open CategoryTheory
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 合成が h であり最初の因子が恒等なら、第二因子と h は同じ Arrow である。 -/
lemma arrowLeftIdentity_cancel {C : Type*} [Category* C] {a b c w : C}
    (f : a ⟶ b) (g : b ⟶ c) (h : a ⟶ c) (hfg : f ≫ g = h)
    (hf : Arrow.mk f = Arrow.mk (𝟙 w)) : Arrow.mk g = Arrow.mk h := by
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff _ _).mp hf
  subst w b
  simp only [eqToHom_refl, Category.comp_id] at hf
  rw [hf, Category.id_comp] at hfg
  exact congrArg Arrow.mk hfg

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
