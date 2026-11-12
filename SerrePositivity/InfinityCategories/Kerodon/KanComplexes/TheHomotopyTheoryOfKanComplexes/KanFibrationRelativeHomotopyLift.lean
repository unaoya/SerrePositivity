module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanFibrationHomotopyLift
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeLeftFibrationPrism

/-!
概要：Kan fibration に沿う指定ホモトピーを、指定部分円柱を保って持ち上げる。
方針：相対 prism の持ち上げを時間が右の全円柱へ戻し、終点を読む。
規約：始点・底・部分円柱は全時刻で厳密に保持する。
使われ方：有限標的射の境界を保つ二入力の同時輸送。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：指定部分円柱と底の全円柱を同時に保つ Kan fibration のホモトピー持ち上げ。
方針：left fibration の相対 prism を持ち上げ、終点と全円柱の制限を計算する。
規約：形状の有限性は不要。使われ方：境界付きの引き戻し二入力輸送。 -/
lemma kanFibration_lift_homotopy_relative {A K E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] (i : A ⟶ K) [Mono i]
    (f : K ⟶ E) {b : K ⟶ B} (H : SSet.Homotopy (f ≫ p) b)
    (a : A ⟶ E) (L : SSet.Homotopy (i ≫ f) a)
    (hL : L.h ≫ p = (i ▷ (Δ[1] : SSet.{u})) ≫ H.h) :
    ∃ g : K ⟶ E, i ≫ g = a ∧ ∃ G : SSet.Homotopy f g,
      (i ▷ (Δ[1] : SSet.{u})) ≫ G.h = L.h ∧ G.h ≫ p = H.h := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanFibration_leftFibration p
  let t := (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h
  let s := (β_ (Δ[1] : SSet.{u}) A).hom ≫ L.h
  have ht : f ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 K ≫ t := H.h₀.symm
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ s = i ≫ f := L.h₀
  have hsp : s ≫ p = (Δ[1] ◁ i) ≫ t := by
    dsimp only [s, t]
    rw [Category.assoc, hL, ← Category.assoc,
      ← BraidedCategory.braiding_naturality_right, Category.assoc]
  obtain ⟨R, hR₀, hRs, hRp⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.leftFibration_lift_prism_relative p i f t s ht hs hsp
  let G := (β_ K (Δ[1] : SSet.{u})).hom ≫ R
  have hG₀ : SSet.ι₀ ≫ G = f := hR₀
  have hGp : G ≫ p = H.h := by
    dsimp only [G]
    rw [Category.assoc, hRp]
    dsimp only [t]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  have hGi : (i ▷ (Δ[1] : SSet.{u})) ≫ G = L.h := by
    dsimp only [G]
    rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc, hRs]
    dsimp only [s]
    rw [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  refine ⟨SSet.ι₁ ≫ G, ?_, ⟨G, hG₀, rfl, ?_⟩, hGi, hGp⟩
  · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, hGi, L.h₁]
  · apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
