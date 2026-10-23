module
public import SerrePositivity.InfinityCategories.Derived.ActionComparisonComposition
public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorIsoWhiskerExchange
/-!
概要：同じ指定比較と合成子の自然性を、全関手同型の等式として輸送する。
方針：実交換則・指定正方形・同じ末尾比較の消去を使う。
規約：新しい比較を選ばない。使われ方：元の導来 kernel 合成子 κ の自然性。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
/-- 同じ ξ の水平合成は、指定した両変数の全関手同型に自然。 -/
lemma comparisonCompositionIso_naturality {X Y Z A B C : SSet.{u}}
    [Quasicategory Y] [Quasicategory B] [Quasicategory C]
    (L₀ : X ⟶ A) (L₁ : Y ⟶ B) (L₂ : Z ⟶ C)
    (F F' : A ⟶ B) (H H' : B ⟶ C) (G G' : X ⟶ Y) (K K' : Y ⟶ Z)
    (a : FunctorIso (L₀ ≫ F) (G ≫ L₁)) (a' : FunctorIso (L₀ ≫ F') (G' ≫ L₁))
    (b : FunctorIso (L₁ ≫ H) (K ≫ L₂)) (b' : FunctorIso (L₁ ≫ H') (K' ≫ L₂))
    (e : FunctorIso F F') (e₀ : FunctorIso G G')
    (d : FunctorIso H H') (d₀ : FunctorIso K K')
    (ha : a ≪≫ e₀.postcomp L₁ = e.precomp L₀ ≪≫ a')
    (hb : b ≪≫ d₀.postcomp L₂ = d.precomp L₁ ≪≫ b') :
    comparisonCompositionIso L₀ L₁ L₂ F G H K a b ≪≫
        FunctorIso.postcomp (e₀.postcomp K ≪≫ d₀.precomp G') L₂ =
      FunctorIso.precomp (e.postcomp H ≪≫ d.precomp F') L₀ ≪≫
        comparisonCompositionIso L₀ L₁ L₂ F' G' H' K' a' b' := by
  have h₀ := F2.functorIso_whisker_exchange e₀ b
  have h₁ := F2.functorIso_whisker_exchange a' d
  calc
    _ = a.postcomp H ≪≫ (b.precomp G ≪≫ (e₀.postcomp K).postcomp L₂) ≪≫
        (d₀.precomp G').postcomp L₂ := by
      simp only [comparisonCompositionIso, F2.functorIso_postcomp_trans, Iso.trans_assoc]
    _ = a.postcomp H ≪≫ ((e₀.postcomp L₁).postcomp H ≪≫ b.precomp G') ≪≫
        (d₀.precomp G').postcomp L₂ := by
      simpa only [F2.functorIso_postcomp_postcomp] using
        congrArg (fun z => a.postcomp H ≪≫ z ≪≫ (d₀.precomp G').postcomp L₂) h₀.symm
    _ = FunctorIso.postcomp (a ≪≫ e₀.postcomp L₁) H ≪≫
        FunctorIso.precomp (b ≪≫ d₀.postcomp L₂) G' := by
      simp only [F2.functorIso_postcomp_trans, F2.functorIso_precomp_trans,
        F2.functorIso_precomp_postcomp, Iso.trans_assoc]
    _ = FunctorIso.postcomp (e.precomp L₀ ≪≫ a') H ≪≫
        FunctorIso.precomp (d.precomp L₁ ≪≫ b') G' := by rw [ha, hb]
    _ = (e.postcomp H).precomp L₀ ≪≫ (a'.postcomp H ≪≫ d.precomp (G' ≫ L₁)) ≪≫
        b'.precomp G' := by
      simp only [F2.functorIso_postcomp_trans, F2.functorIso_precomp_trans,
        F2.functorIso_precomp_postcomp, F2.functorIso_precomp_precomp, Iso.trans_assoc]
    _ = (e.postcomp H).precomp L₀ ≪≫ (d.precomp (L₀ ≫ F') ≪≫ a'.postcomp H') ≪≫
        b'.precomp G' := by rw [h₁]
    _ = _ := by
      simp only [comparisonCompositionIso, F2.functorIso_precomp_trans,
        F2.functorIso_precomp_precomp, Iso.trans_assoc]
end
end SerrePositivity.InfinityCategories
