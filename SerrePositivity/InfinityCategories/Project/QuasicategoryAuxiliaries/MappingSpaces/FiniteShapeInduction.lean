module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FiniteCoproductPredicate
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-!
概要：空形状・単体・単射側のある pushout から全有限単体集合へ帰納する。
方針：有限和を pushout から導き、次元と骨格の帰納で有限セルを付着する。
規約：元の有限形状を同型まで保持し、有限半順序形状へ置き換えない。
使われ方：quasicategory の有限極限・有限余極限の一般生成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 空形状・標準単体・単射側のある pushout に閉じる性質は全有限形状で成り立つ。 -/
lemma finiteShape_induction_of_pushouts (P : SSet.{u} → Prop)
    (hIso : ∀ {A B : SSet.{u}}, (A ≅ B) → P A → P B)
    (hEmpty : ∀ X : SSet.{u}, P (⊥ : X.Subcomplex))
    (hSimplex : ∀ n : ℕ, P (Δ[n] : SSet.{u}))
    (hPushout : ∀ {A B C D : SSet.{u}} {f : A ⟶ B} {g : A ⟶ C}
      {i : B ⟶ D} {j : C ⟶ D} [Mono g],
      IsPushout f g i j → P A → P B → P C → P D)
    (X : SSet.{u}) [X.Finite] : P X := by
  have : InitialMonoClass SSet.{u} := InitialMonoClass.of_isInitial
    (Subcomplex.isInitialBot (X := (Δ[0] : SSet.{u}))) (by
      intro Y
      rw [NatTrans.mono_iff_mono_app]
      intro n
      rw [mono_iff_injective]
      intro a
      exact a.property.elim)
  have h0 : P (⊥_ SSet.{u}) := hIso
    (Subcomplex.isInitialBot.uniqueUpToIso initialIsInitial) (hEmpty (Δ[0] : SSet.{u}))
  have hSum {I : Type u} [Finite I] (F : I → SSet.{u}) (hF : ∀ i, P (F i)) :
      P (∐ F) := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.finiteCoproduct_predicate_of_pushouts P hIso h0 hPushout F hF
  have hsk (Y : SSet.{u}) (d : ℕ) [Y.HasDimensionLT d] : Y.skeleton d = ⊤ := by
    apply (Subcomplex.eq_top_iff_of_hasDimensionLT _ d).mpr
    intro i hi x hx
    exact Y.mem_skeleton x hi
  have hdim : ∀ d (Y : SSet.{u}) [Y.Finite] [Y.HasDimensionLT d], P Y := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro Y hfin hdim
      let e := (⊥ : Y.Subcomplex).ι
      have hs : ∀ n, n ≤ d → P (SSet.skeletonOfMono e n) := by
        intro n
        induction n with
        | zero =>
          intro hn
          simpa only [SSet.skeletonOfMono_zero, e, Subfunctor.range_ι] using hEmpty Y
        | succ n hn =>
          intro hnd
          have : Finite (SSet.relativeCellComplexOfMono.Cell e n) :=
            Finite.of_injective
              (fun c => (⟨c.simplex, c.nonDegenerate⟩ : Y.nonDegenerate n)) (by
                intro a b h
                apply SSet.relativeCellComplexOfMono.Cell.ext
                exact congrArg Subtype.val h)
          have hb : P (∂Δ[n] : SSet.{u}) := ih n (Nat.lt_of_succ_le hnd) _
          exact hPushout (SSet.relativeCellComplexOfMono.isPushout e n)
            (hSum _ (fun _ => hb)) (hn (Nat.le_of_succ_le hnd))
            (hSum _ (fun _ => hSimplex n))
      have ht : SSet.skeletonOfMono e d = ⊤ := by
        simp only [SSet.skeletonOfMono, OrderHom.coe_mk, hsk Y d, sup_top_eq]
      have hp := hs d le_rfl
      rw [ht] at hp
      exact hIso (Subcomplex.topIso Y) hp
  obtain ⟨d, hd⟩ := X.hasDimensionLT_of_finite
  exact hdim d X

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
