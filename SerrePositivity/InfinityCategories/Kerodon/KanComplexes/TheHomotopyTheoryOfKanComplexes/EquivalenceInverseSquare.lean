module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FamilyEquivalenceReflection

/-!
概要：指定同値を持つ全族の正方形を、同じ指定逆の正方形へ移す。
方針：元の同型と指定された単位・余単位を合成して反映する。
規約：逆の選択を変更しない。使われ方：G8 の表現の頂点同型の逆の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet

namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：同じ指定同値の順射による可換正方形から、指定逆による全族同型を得る。
方針：順射で前合成し、指定単位・余単位を相殺して反映する。
規約：同じ逆の実射を保持。使われ方：G8 の元の値比較の逆の自然性。 -/
def functorIsoInverseSquare {A B C D : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory C] [Quasicategory D]
    (a : QCatEquivalence A B) (b : QCatEquivalence C D) (f : A ⟶ C) (g : B ⟶ D)
    (h : FunctorIso (f ≫ b.hom) (a.hom ≫ g)) :
    FunctorIso (g ≫ b.inv) (a.inv ≫ f) := by
  apply functorIsoOfPrecompEquivalence a.hom a.isQCatEquivalence
  have h₁ := FunctorIso.postcomp h.symm b.inv
  have h₂ := FunctorIso.precomp b.homInvIso f
  have h₃ := (FunctorIso.postcomp a.homInvIso f).symm
  simp only [Category.assoc, Category.id_comp, Category.comp_id] at h₁ h₂ h₃
  exact h₁ ≪≫ h₂ ≪≫ h₃

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
