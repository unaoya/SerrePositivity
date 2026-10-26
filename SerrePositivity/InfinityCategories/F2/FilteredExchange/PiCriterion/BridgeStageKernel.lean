module

public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.FilteredSpaceBridgeInput
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PiCriterion.PairPathEquality

/-!
概要：D の正次数の後続段階での同一視を、段階に自然な Kan 標的へ反映する。
方針：D の同じ transition による等式を後合成し、脚の Homotopy で戻す。
規約：D の抽象構造を直接消費する。群の余極限は構成しない。
使われ方：全空間比較の正次数の単射性。
-/

@[expose] public section
noncomputable section
universe u w
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.PiCriterion
open KST.Spectra

/-- D が後続段階で同一視する二つの類は、段階にホモトピーまで自然な標的でも等しい。 -/
lemma bridge_stage_positive_kernel {I : Type u} [PartialOrder I]
    (X : I → KanObject.{w}) (A T : KanObject.{w})
    (τ : ∀ {i j : I}, i ≤ j → ((X i).obj ⟶ (X j).obj))
    (l : ∀ i : I, (X i).obj ⟶ A.obj)
    (h : DGBarCompactSpacePiData X A τ l)
    (s : ∀ i : I, (X i).obj ⟶ T.obj)
    (hstage : ∀ (i j : I) (hij : i ≤ j), Nonempty (Homotopy (s i) (τ hij ≫ s j)))
    (n : ℕ) (i : I) (y : (X i).obj _⦋0⦌)
    (a b : KanHomotopyGroup (X i).obj n y)
    (hab : dgBarCompactPiMap n (l i) y a = dgBarCompactPiMap n (l i) y b) :
    KanHomotopyGroup.map (s i) rfl a = KanHomotopyGroup.map (s i) rfl b := by
  obtain ⟨j, hij, hj⟩ := h.positive_equal_at_stage n i y a b hab
  obtain ⟨H⟩ := hstage i j hij
  apply (homotopy_map_equality_iff H n y a b).mpr
  have hm (c : KanHomotopyGroup (X i).obj n y) :
      KanHomotopyGroup.map (τ hij ≫ s j) rfl c =
        KanHomotopyGroup.map (s j) rfl (dgBarCompactPiMap n (τ hij) y c) :=
    DFunLike.congr_fun (KanHomotopyGroup.map_comp (τ hij) rfl (s j) rfl rfl) c
  exact (hm a).trans ((congrArg (KanHomotopyGroup.map (s j) rfl) hj).trans (hm b).symm)

end SerrePositivity.InfinityCategories.F2.PiCriterion
