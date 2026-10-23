module

public import SerrePositivity.InfinityCategories.F1.Transport.SimplexInvertingRestriction
public import Mathlib.CategoryTheory.LiftingProperties.Limits

/-!
概要：頂点条件が元の射で反映されれば、全部分複体への制限は元の射の pullback。
方針：同じ頂点条件で元の射を全部分複体へ持ち上げ、包含後の等式で普遍性を示す。
規約：充填性やモデル構造の追加仮定は不要。
使われ方：指定辺を保つ相対 Hom に自明 Kan 制限を移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 頂点条件を反映する射の全部分複体への制限は、元の射の実際の pullback。 -/
lemma fullRestriction_isPullback {X Y : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (Q : Y _⦋0⦌ → Prop)
    (p : (fullSubcomplexOnVertices X P : SSet.{u}) ⟶ fullSubcomplexOnVertices Y Q)
    (q : X ⟶ Y)
    (h : p ≫ (fullSubcomplexOnVertices Y Q).ι = (fullSubcomplexOnVertices X P).ι ≫ q)
    (hr : ∀ x, Q (q.app (Opposite.op ⦋0⦌) x) → P x) :
    IsPullback (fullSubcomplexOnVertices X P).ι p q (fullSubcomplexOnVertices Y Q).ι := by
  refine IsPullback.mk' h.symm ?_ ?_
  · intro T a b ha hb
    exact (cancel_mono (fullSubcomplexOnVertices X P).ι).mp ha
  · intro T a b hab
    let L := fullSubcomplexLift P a (by
      intro t
      apply hr
      have ht := congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) t) hab
      change q.app (Opposite.op ⦋0⦌) (a.app (Opposite.op ⦋0⦌) t) =
        (b.app (Opposite.op ⦋0⦌) t).val at ht
      rw [ht]
      exact fullSubcomplexOnVertices_vertex (b.app (Opposite.op ⦋0⦌) t))
    refine ⟨L, fullSubcomplexLift_ι _ _ _, ?_⟩
    apply (cancel_mono (fullSubcomplexOnVertices Y Q).ι).mp
    rw [Category.assoc, h, ← Category.assoc, fullSubcomplexLift_ι]
    exact hab

/-- 同じ頂点条件を反映する全部分複体への制限は、元の自明 Kan 性を保つ。 -/
lemma fullRestriction_trivialKanFibration {X Y : SSet.{u}} (P : X _⦋0⦌ → Prop)
    (Q : Y _⦋0⦌ → Prop)
    (p : (fullSubcomplexOnVertices X P : SSet.{u}) ⟶ fullSubcomplexOnVertices Y Q)
    (q : X ⟶ Y) [TrivialKanFibration q]
    (h : p ≫ (fullSubcomplexOnVertices Y Q).ι = (fullSubcomplexOnVertices X P).ι ≫ q)
    (hr : ∀ x, Q (q.app (Opposite.op ⦋0⦌) x) → P x) : TrivialKanFibration p :=
  ⟨trivialKanFibrations.of_isPullback (fullRestriction_isPullback P Q p q h hr)
    TrivialKanFibration.mem⟩

end SerrePositivity.InfinityCategories
