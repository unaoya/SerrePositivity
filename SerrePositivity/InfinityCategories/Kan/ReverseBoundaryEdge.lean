module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.FibrationInverseEdge
public import SerrePositivity.InfinityCategories.Kan.HomotopyGroups

/-!
概要：基点から fiber の頂点へ向かう辺を、逆の底の辺の連結射の持ち上げへ戻す。
方針：終点を一時的な全空間の基点とし、既存の逆元三角形の相対充填を使う。
規約：fiber の零次数に群構造を仮定しない。
使われ方：Goerss–Jardine I §8。零 loop 成分の反可換性の向きの基本段。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Kan
open SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：基点から fiber の頂点への辺は、底の逆元の連結射の正向きの充填に直せる。
方針：終点へ基点を移し、逆元三角形を相対充填し、元の基点へ戻す。
規約：与えた fiber の頂点を最後の面として厳密に保つ。
使われ方：Goerss–Jardine I §8。零次数の path の逆向きと底の群の逆元の対応。 -/
theorem exists_reverse_boundary_edge {E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (e : E _⦋0⦌) {s t : B.PtSimplex 1 (p.app _ e)}
    (a : (KanFiber p (p.app _ e)).PtSimplex 0 (fiberPoint p e))
    (T : (Δ[1] : SSet.{u}) ⟶ E) (hT : T ≫ p = s.map)
    (h₀ : stdSimplex.δ (0 : Fin 2) ≫ T = a.map ≫ fiberι p (p.app _ e))
    (h₁ : stdSimplex.δ (1 : Fin 2) ≫ T = SSet.const e)
    (m : PtSimplex.MulStruct t s .const (0 : Fin 1)) :
    ∃ L : BoundaryLift p e t, L.boundary = a := by
  let av := (fiberι p (p.app _ e)).app _ (PtSimplex.equiv₀ (fiberPoint p e) a)
  have ha : a.map ≫ fiberι p (p.app _ e) = SSet.const av := by
    rw [a.map_eq_const_equiv₀, const_comp]
  have hpav : p.app _ av = p.app _ e := by
    have h := congrArg (fun f ↦ f.app _ (PtSimplex.equiv₀ (fiberPoint p e) a))
      (fiberι_comp p (p.app _ e))
    have hc : (SSet.const (X := KanFiber p (p.app _ e)) (p.app _ e)).app _
        (PtSimplex.equiv₀ (fiberPoint p e) a) = p.app _ e := by simp
    simpa only [NatTrans.comp_app, types_comp_apply, av] using h.trans hc
  have hb : (𝟙 B : B ⟶ B).app _ (p.app _ e) = p.app _ av := hpav.symm
  let L : BoundaryLift p av (mapSimplex (𝟙 B) hb s) :=
    { map := T
      map_comp := by simpa only [mapSimplex, Category.comp_id] using hT
      face_eq j hj := by
        fin_cases j
        · exact h₀.trans ha
        · exact (hj rfl).elim }
  have m' : PtSimplex.MulStruct (mapSimplex (𝟙 B) hb t) (mapSimplex (𝟙 B) hb s)
      .const (0 : Fin 1) := by
    simpa only [mapSimplex_const] using mapMulStruct (𝟙 B) hb m
  obtain ⟨K, hK, hK₀, hK₁⟩ := exists_inverse_edge p av L m'
  let R : BoundaryLift p e t :=
    { map := K
      map_comp := by simpa only [mapSimplex, Category.comp_id] using hK
      face_eq j hj := by
        fin_cases j
        · exact hK₀.trans h₁
        · exact (hj rfl).elim }
  refine ⟨R, ?_⟩
  ext : 1
  apply fiber_hom_ext p (p.app _ e)
  rw [R.boundary_ι, ha]
  exact hK₁

end
end SerrePositivity.InfinityCategories.Kan

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.exists_reverse_boundary_edge := _root_.SerrePositivity.InfinityCategories.Kan.exists_reverse_boundary_edge
