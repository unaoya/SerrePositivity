module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.OptionCoproductIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.PushoutCornerComparison
public import Mathlib.CategoryTheory.Limits.Constructions.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.StrictInitial
public import Mathlib.Data.Fintype.Option

/-!
概要：同型と単射側のある pushout に閉じる性質を有限余積へ伝える。
方針：二項余積を始対象上の pushout とし、有限添字を Option で帰納する。
規約：始対象からの射の単射性を仮定する一般の圏で述べる。
使われ方：有限単体集合のセル帰納に必要な有限和の段階。
-/

@[expose] public section
noncomputable section
universe v u w
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 始対象と形状 pushout に閉じる性質は、有限余積にも閉じる。 -/
lemma finiteCoproduct_predicate_of_pushouts {C : Type u} [Category.{v} C]
    [HasInitial C] [InitialMonoClass C] [HasPushouts C]
    [HasBinaryCoproducts C] [HasCoproducts.{w} C] (P : C → Prop)
    (hIso : ∀ {A B : C}, (A ≅ B) → P A → P B) (h0 : P (⊥_ C))
    (hPushout : ∀ {A B D T : C} {f : A ⟶ B} {g : A ⟶ D}
      {i : B ⟶ T} {j : D ⟶ T} [Mono g],
      IsPushout f g i j → P A → P B → P D → P T)
    {J : Type w} [Finite J] (F : J → C) (hF : ∀ j, P (F j)) : P (∐ F) := by
  have hbin {A B : C} (hA : P A) (hB : P B) : P (A ⨿ B) := by
    apply hIso (coprodIsoPushout A B).symm
    exact hPushout (IsPushout.of_hasPushout (initial.to A) (initial.to B)) h0 hA hB
  have hall : ∀ (I : Type w) [Finite I] (G : I → C), (∀ i, P (G i)) → P (∐ G) := by
    intro I _
    apply Finite.induction_empty_option
      (P := fun I => ∀ G : I → C, (∀ i, P (G i)) → P (∐ G))
    · intro I K e ih G hG
      exact hIso (Sigma.whiskerEquiv e (fun _ => Iso.refl _))
        (ih (fun i => G (e i)) (fun i => hG (e i)))
    · intro G _
      have hi : IsInitial (∐ G) := IsInitial.ofUniqueHom
        (fun Y => Sigma.desc (fun i => PEmpty.elim i)) (by
          intro Y m
          apply Sigma.hom_ext
          intro i
          exact PEmpty.elim i)
      exact hIso (initialIsInitial.uniqueUpToIso hi) h0
    · intro I _ ih G hG
      apply hIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.optionCoproductIso G).symm
      exact hbin (hG none) (ih _ (fun i => hG (some i)))
  exact hall J F hF

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
