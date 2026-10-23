module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SimultaneousRelativeCylinderDetection
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.IntervalPullbackRelativeInputTransport

/-!
概要：任意の Kan 引き戻し射の二入力を、元の境界円柱を保って元の全空間へ移す。
方針：共通境界付き同時検出を二入力射の相対持ち上げへ渡す。
規約：元の境界包含 k を保持。使われ方：元の二入力の場合への相対的帰着。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：任意の有限標的射は、元の全境界円柱を保って元の二入力を持つ射へ移る。
方針：同時検出の円柱を標的の二入力射に沿って相対的に持ち上げる。
規約：厳密な境界入力と全円柱の制限。使われ方：一般の相対有限比較の入力還元。 -/
lemma kanCospan_relative_input_reduction {K R E D H B : SSet.{u}}
    [K.Finite] [Quasicategory B] [IsFilteredInfinity B]
    (p : R ⟶ B) [LeftFibration p] (q : E ⟶ B) [LeftFibration q]
    (r : D ⟶ B) [LeftFibration r] (c : R ⟶ E) (d : R ⟶ D)
    (hc : c ≫ q = p) (hd : d ≫ r = p) (f : E ⟶ H) (g : D ⟶ H)
    (k : R ⟶ intervalPullback (continuousKanReplacement.map f) (continuousKanReplacement.map g))
    (hkl : k ≫ intervalPullbackLeft (continuousKanReplacement.map f)
      (continuousKanReplacement.map g) = c ≫ continuousKanReplacementUnit.app E)
    (hkr : k ≫ intervalPullbackRight (continuousKanReplacement.map f)
      (continuousKanReplacement.map g) = d ≫ continuousKanReplacementUnit.app D)
    (A : K.Subcomplex) (a : (A : SSet.{u}) ⟶ R)
    (e : K ⟶ intervalPullback (continuousKanReplacement.map f) (continuousKanReplacement.map g))
    (he : A.ι ≫ e = a ≫ k) :
    ∃ (a' : (A : SSet.{u}) ⟶ R) (u : K ⟶ E) (v : K ⟶ D),
      A.ι ≫ u = a' ≫ c ∧ A.ι ≫ v = a' ≫ d ∧
      ∃ T : SSet.Homotopy a a',
      ∃ e' : K ⟶ intervalPullback (continuousKanReplacement.map f) (continuousKanReplacement.map g),
        A.ι ≫ e' = a' ≫ k ∧
        e' ≫ intervalPullbackLeft (continuousKanReplacement.map f)
          (continuousKanReplacement.map g) = u ≫ continuousKanReplacementUnit.app E ∧
        e' ≫ intervalPullbackRight (continuousKanReplacement.map f)
          (continuousKanReplacement.map g) = v ≫ continuousKanReplacementUnit.app D ∧
      ∃ G : SSet.Homotopy e e', (A.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h = T.h ≫ k := by
  have hu : (a ≫ c) ≫ continuousKanReplacementUnit.app E = A.ι ≫
      (e ≫ intervalPullbackLeft (continuousKanReplacement.map f)
        (continuousKanReplacement.map g)) := by
    have h := congrArg (fun t ↦ t ≫ intervalPullbackLeft
      (continuousKanReplacement.map f) (continuousKanReplacement.map g)) he
    simpa only [Category.assoc, hkl] using h.symm
  have hv : (a ≫ d) ≫ continuousKanReplacementUnit.app D = A.ι ≫
      (e ≫ intervalPullbackRight (continuousKanReplacement.map f)
        (continuousKanReplacement.map g)) := by
    have h := congrArg (fun t ↦ t ≫ intervalPullbackRight
      (continuousKanReplacement.map f) (continuousKanReplacement.map g)) he
    simpa only [Category.assoc, hkr] using h.symm
  obtain ⟨b, t, s, w, hs, hw, T, U, V, hU, hV⟩ :=
    continuousKanLeftFibration_pair_relative_cylinder_detection p q r c d hc hd A a
      (e ≫ intervalPullbackLeft _ _) (e ≫ intervalPullbackRight _ _) hu hv
  let L : SSet.Homotopy (A.ι ≫ e) ((t ≫ vertexFiberι p b) ≫ k) :=
    { h := T.h ≫ k
      h₀ := by
        change SSet.ι₀ ≫ T.h ≫ k = A.ι ≫ e
        rw [← Category.assoc, T.h₀, ← he]
      h₁ := by
        change SSet.ι₁ ≫ T.h ≫ k = (t ≫ vertexFiberι p b) ≫ k
        rw [← Category.assoc, T.h₁]
      rel := (functorHomotopyPostcomp T k).rel }
  have hU' : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ U.h = L.h ≫
      intervalPullbackLeft (continuousKanReplacement.map f) (continuousKanReplacement.map g) := by
    change _ = (T.h ≫ k) ≫ _
    rw [Category.assoc, hkl, hU]
  have hV' : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ V.h = L.h ≫
      intervalPullbackRight (continuousKanReplacement.map f) (continuousKanReplacement.map g) := by
    change _ = (T.h ≫ k) ≫ _
    rw [Category.assoc, hkr, hV]
  obtain ⟨e', he', hl, hr, G, hG, _⟩ := intervalPullback_transport_inputs_relative
    (continuousKanReplacement.map f) (continuousKanReplacement.map g) A.ι e
    (s ≫ vertexFiberι q b ≫ continuousKanReplacementUnit.app E)
    (w ≫ vertexFiberι r b ≫ continuousKanReplacementUnit.app D) U V _ L hU' hV'
  refine ⟨t ≫ vertexFiberι p b, s ≫ vertexFiberι q b, w ≫ vertexFiberι r b,
    ?_, ?_, T, e', he', hl, hr, G, hG⟩
  · rw [← Category.assoc, hs, Category.assoc, vertexFiberMap_ι]
    rfl
  · rw [← Category.assoc, hw, Category.assoc, vertexFiberMap_ι]
    rfl

end SerrePositivity.InfinityCategories.F2
