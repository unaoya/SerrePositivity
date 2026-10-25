module

public import SerrePositivity.InfinityCategories.F2.Presentable.CofinalSimplexTowerGluing
public import SerrePositivity.InfinityCategories.F2.Presentable.SequentialNerveUniverse

/-!
概要：小さい形状の全図式列を、native な可算 nerve 上の全図式へ貼り合わせる。
方針：指定形状同型と宇宙同型で標準単体列へ移し、公開 P の貼合入口を使う。
規約：全射の厳密な制限を保持する。使われ方：二表示の全比較と大域余錐の貼合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits

/-- 標準単体の逆宇宙同型は全前置包含と可換。 -/
lemma uliftStdSimplexIso_inv_prefix {m n : ℕ} (h : m ≤ n) :
    simplexPrefix.{u + 1} h ≫ (uliftStdSimplexIso.{u, u + 1} n).inv =
      (uliftStdSimplexIso.{u, u + 1} m).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (simplexPrefix.{u} h) := by
  have hu : (SSet.uliftFunctor.{u + 1, u}).map (simplexPrefix.{u} h) ≫
      (uliftStdSimplexIso.{u, u + 1} n).hom =
      (uliftStdSimplexIso.{u, u + 1} m).hom ≫ simplexPrefix.{u + 1} h := rfl
  apply (cancel_epi (uliftStdSimplexIso.{u, u + 1} m).hom).mp
  rw [← Category.assoc, ← hu, Category.assoc, Iso.hom_inv_id,
    Category.comp_id, Iso.hom_inv_id_assoc]

/-- 指定同型で前置単体列となる全図式列は、同じ native な可算図式へ貼り合わさる。 -/
lemma exists_nativeDiagram_of_shapeTower {X : SSet.{u + 1}}
    (d : ℕ → ℕ) (hm : Monotone d) (hd : ∀ m, ∃ n, m ≤ d n)
    (K : ℕ → SSet.{u}) (i : ∀ n, K n ⟶ K (n + 1))
    (e : ∀ n, K n ≅ (Δ[d n] : SSet.{u}))
    (he : ∀ n, i n ≫ (e (n + 1)).hom =
      (e n).hom ≫ simplexPrefix (hm (Nat.le_succ n)))
    (F : ∀ n, (SSet.uliftFunctor.{u + 1, u}).obj (K n) ⟶ X)
    (hf : ∀ n, (SSet.uliftFunctor.{u + 1, u}).map (i n) ≫ F (n + 1) = F n) :
    ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (ULift.{u} ℕ)) ⟶ X,
      ∀ n, (SSet.uliftFunctor.{u + 1, u}).map (sequentialNerveInitialSimplex (d n)) ≫ G =
        (SSet.uliftFunctor.{u + 1, u}).map (e n).inv ≫ F n := by
  have hi n : simplexPrefix (hm (Nat.le_succ n)) ≫ (e (n + 1)).inv =
      (e n).inv ≫ i n := by
    apply (cancel_epi (e n).hom).mp
    rw [← Category.assoc, ← he n, Category.assoc, Iso.hom_inv_id,
      Category.comp_id, Iso.hom_inv_id_assoc]
  let f n : (Δ[d n] : SSet.{u + 1}) ⟶ X :=
    (uliftStdSimplexIso.{u, u + 1} (d n)).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (e n).inv ≫ F n
  have hstep n : simplexPrefix (hm (Nat.le_succ n)) ≫ f (n + 1) = f n := by
    dsimp only [f]
    rw [← Category.assoc (simplexPrefix _) (uliftStdSimplexIso (d (n + 1))).inv,
      uliftStdSimplexIso_inv_prefix]
    simp only [Category.assoc]
    rw [← Category.assoc ((SSet.uliftFunctor.{u + 1, u}).map (simplexPrefix _)),
      ← (SSet.uliftFunctor.{u + 1, u}).map_comp, hi n,
      (SSet.uliftFunctor.{u + 1, u}).map_comp, Category.assoc, hf n]
  obtain ⟨H, hH⟩ := exists_sequentialDiagram_of_cofinalSimplices d hm hd f hstep
  refine ⟨sequentialNerveUniverseIso.hom ≫ H, fun n ↦ ?_⟩
  rw [← Category.assoc, sequentialNerveUniverseIso_initialSimplex, Category.assoc, hH n]
  dsimp only [f]
  rw [Iso.hom_inv_id_assoc]

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
