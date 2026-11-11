module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.GluedFiberDetection
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PullbackHomotopy

/-!
概要：共通境界を持つ二つの有限図式の輸送を、元の引き戻し内の境界の輸送へまとめる。
方針：貼り合わせた底の収縮を持ち上げ、全時刻の底の一致で引き戻しへ入れる。
規約：境界の有限因子分解に単射性を要求しない。
使われ方：積比較の相対検出と単射側の境界の追跡。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：有限図式の共通 fiber への輸送は、指定境界の引き戻し内の輸送を与える。
方針：境界での二つの底の一致を pushout へ延長し、両円柱を引き戻しで貼る。
規約：元の境界射と二つの円柱を保持する。使われ方：同じ fiber でのホモトピーの検出。 -/
lemma leftFibration_glued_pullback_transport {A K L E D B : SSet.{u}}
    [A.Finite] [K.Finite] [L.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : E ⟶ B) [LeftFibration p] (q : D ⟶ B) [LeftFibration q]
    (i : A ⟶ K) (j : A ⟶ L) (f : K ⟶ E) (g : L ⟶ D)
    (a : A ⟶ pullback p q)
    (ha : a ≫ pullback.fst p q = i ≫ f) (hb : a ≫ pullback.snd p q = j ≫ g) :
    ∃ b : B _⦋0⦌, ∃ s : K ⟶ vertexFiber p b, ∃ t : L ⟶ vertexFiber q b,
      ∃ Hs : SSet.Homotopy f (s ≫ vertexFiberι p b),
      ∃ Ht : SSet.Homotopy g (t ≫ vertexFiberι q b),
      ∃ Ha : SSet.Homotopy a (fiberPairToPullback p q b (i ≫ s) (j ≫ t)),
        Ha.h ≫ pullback.fst p q = (i ▷ (Δ[1] : SSet.{u})) ≫ Hs.h ∧
        Ha.h ≫ pullback.snd p q = (j ▷ (Δ[1] : SSet.{u})) ≫ Ht.h := by
  have h : i ≫ f ≫ p = j ≫ g ≫ q := by
    rw [← Category.assoc, ← Category.assoc, ← ha, ← hb,
      Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨b, s, t, Hs, Ht, he⟩ :=
    leftFibration_glued_finite_fiber_detection p q i j f g h
  let a' := fiberPairToPullback p q b (i ≫ s) (j ≫ t)
  let H : SSet.Homotopy (a ≫ pullback.fst p q) (a' ≫ pullback.fst p q) := {
    h := (i ▷ (Δ[1] : SSet.{u})) ≫ Hs.h
    h₀ := by rw [SSet.ι₀_comp_assoc, Hs.h₀]; exact ha.symm
    h₁ := by
      change SSet.ι₁ ≫ (i ▷ (Δ[1] : SSet.{u})) ≫ Hs.h = a' ≫ pullback.fst p q
      rw [SSet.ι₁_comp_assoc, Hs.h₁]
      simp only [a', fiberPairToPullback, pullback.lift_fst, Category.assoc]
    rel := (functorHomotopyPrecomp Hs i).rel }
  let G : SSet.Homotopy (a ≫ pullback.snd p q) (a' ≫ pullback.snd p q) := {
    h := (j ▷ (Δ[1] : SSet.{u})) ≫ Ht.h
    h₀ := by rw [SSet.ι₀_comp_assoc, Ht.h₀]; exact hb.symm
    h₁ := by
      change SSet.ι₁ ≫ (j ▷ (Δ[1] : SSet.{u})) ≫ Ht.h = a' ≫ pullback.snd p q
      rw [SSet.ι₁_comp_assoc, Ht.h₁]
      simp only [a', fiberPairToPullback, pullback.lift_snd, Category.assoc]
    rel := (functorHomotopyPrecomp Ht j).rel }
  exact ⟨b, s, t, Hs, Ht, pullbackHomotopy p q H G he,
    pullbackHomotopy_fst p q H G he, pullbackHomotopy_snd p q H G he⟩

end SerrePositivity.InfinityCategories.F2
