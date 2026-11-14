module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalDiagram
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalReplacementHomotopyPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.IntervalReplacementPath
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.KanBoundaryHomotopyFinalExtension
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.RelativeHomotopyFactorThrough

/-!
概要：境界固定の相対ホモトピー持ち上げから、区間 path 置換の終点射の厳密な持ち上げを得る。
方針：指定境界 path を終点固定で延長し、元の比較を境界 path を保って因子分解する。
規約：元の境界の入力と全 path の両方を厳密に保持。
使われ方：有限相対持ち上げによる弱同値性の判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：境界固定でホモトピーまで持ち上がれば、path 置換の終点射には厳密な持ち上げがある。
方針：元の境界 path の逆向き延長と相対外ホーン充填。
規約：充填性 h はこの境界に限る。使われ方：終点射の全標準境界に対する持ち上げ。 -/
lemma intervalReplacementEndpoint_relative_lift {K X Y : SSet.{u}} [KanComplex Y]
    (A : K.Subcomplex) (f : X ⟶ Y) (u : (A : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement f) (e : K ⟶ Y)
    (he : u ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f = A.ι ≫ e)
    (h : ∀ (a : (A : SSet.{u}) ⟶ X) (b : K ⟶ Y), A.ι ≫ b = a ≫ f →
      ∃ r : K ⟶ X, A.ι ≫ r = a ∧ ∃ G : SSet.Homotopy b (r ≫ f),
        (A.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h =
          fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ a ≫ f) :
    ∃ v : K ⟶ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacement f, A.ι ≫ v = u ∧ v ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementEndpoint f = e := by
  let a := u ≫ pullback.snd ((_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalEndpointNatTrans 0).app Y) f
  let P := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementPathHomotopy f u
  let L : SSet.Homotopy (a ≫ f) (A.ι ≫ e) :=
    { h := P.h
      h₀ := P.h₀
      h₁ := by
        change SSet.ι₁ ≫ P.h = A.ι ≫ e
        rw [P.h₁, he]
      rel := P.rel }
  obtain ⟨b, hb, S, hS⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.kanComplex_extend_boundary_homotopy_final A e (a ≫ f) L
  obtain ⟨r, hr, G, hG⟩ := h a b hb
  let L' : SSet.Homotopy (A.ι ≫ b) (A.ι ≫ e) :=
    { h := L.h
      h₀ := by
        change SSet.ι₀ ≫ L.h = A.ι ≫ b
        rw [L.h₀, hb]
      h₁ := L.h₁
      rel := L.rel }
  have hG' : (A.ι ▷ (Δ[1] : SSet.{u})) ≫ G.h =
      fst (A : SSet.{u}) (Δ[1] : SSet.{u}) ≫ A.ι ≫ b := by
    rw [hG, hb]
  obtain ⟨R, hR⟩ := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.exists_relativeHomotopyFactorThrough A G S L' hG' hS
  refine ⟨_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementHomotopyPoint f r e R, ?_,
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementHomotopyPoint_endpoint f r e R⟩
  exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.intervalReplacementHomotopyPoint_restrict f r e R A.ι u hr hR

end SerrePositivity.InfinityCategories.Project.FilteredExchange
