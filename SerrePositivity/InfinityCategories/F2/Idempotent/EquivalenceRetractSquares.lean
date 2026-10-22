module

public import SerrePositivity.InfinityCategories.Core.EquivalenceCalculus

/-!
概要：全自然同型で可換な retract 正方形に沿って、元の関手の同値性を戻す。
方針：大きい比較射の逆を両側の retract と合成し、全自然同型で両逆性を証明する。
規約：元の小さい比較射そのものが同値。写像空間や π₀ の全単射だけに弱めない。
使われ方：普遍錐・余錐の相対始対象性の retract 閉性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 全自然同型で可換な実際の retract 正方形は、元の比較射の同値性を反映する。 -/
lemma isQCatEquivalence_of_retractSquares {A B A' B' : SSet.{u}}
    [Quasicategory A] [Quasicategory B] [Quasicategory A'] [Quasicategory B']
    (f : A ⟶ B) (g : A' ⟶ B') (iA : A ⟶ A') (rA : A' ⟶ A)
    (iB : B ⟶ B') (rB : B' ⟶ B)
    (hA : FunctorIso (iA ≫ rA) (𝟙 A)) (hB : FunctorIso (iB ≫ rB) (𝟙 B))
    (hi : FunctorIso (f ≫ iB) (iA ≫ g))
    (hr : FunctorIso (g ≫ rB) (rA ≫ f)) (hg : IsQCatEquivalence g) :
    IsQCatEquivalence f := by
  let e := hg.choose
  let v := iB ≫ e.inv ≫ rA
  refine ⟨v, ⟨?_⟩, ⟨?_⟩⟩
  · have h₁ : FunctorIso (f ≫ v) (iA ≫ g ≫ e.inv ≫ rA) := by
      simpa only [v, Category.assoc] using (FunctorIso.postcomp hi (e.inv ≫ rA))
    have h₂ : FunctorIso (iA ≫ g ≫ e.inv ≫ rA) (iA ≫ rA) := by
      simpa only [e, IsQCatEquivalence.choose, Category.assoc, Category.comp_id,
        Category.id_comp] using
        (FunctorIso.postcomp (FunctorIso.precomp e.homInvIso iA) rA)
    exact h₁ ≪≫ h₂ ≪≫ hA
  · have h₁ : FunctorIso (v ≫ f) (iB ≫ e.inv ≫ g ≫ rB) := by
      simpa only [v, Category.assoc] using (FunctorIso.precomp hr.symm (iB ≫ e.inv))
    have h₂ : FunctorIso (iB ≫ e.inv ≫ g ≫ rB) (iB ≫ rB) := by
      simpa only [e, IsQCatEquivalence.choose, Category.assoc, Category.comp_id,
        Category.id_comp] using
        (FunctorIso.precomp (FunctorIso.postcomp e.invHomIso rB) iB)
    exact h₁ ≪≫ h₂ ≪≫ hB

end SerrePositivity.InfinityCategories.F2.Idempotent
