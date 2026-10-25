module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.FullSimplexComponents
/-!
概要：全体 HA 項の切断合成を独立した成分として保持する。
方針：既存の cutComposite を全頂点集合に適用し、端点・次数輸送の補題を供給する。
規約：方程式や閉性を仮定しない。
使われ方：パラメーター側の零・単位による切断合成の消去。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]

def dgCoherentBarFullComposite {n : ℕ} (s : SimplexData R C (n + 1)) (i : Fin n) :=
  s.cutComposite Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ))
    (coherentDiagramTop_card n) (coherentDiagramTop_min n) (coherentDiagramTop_max n)
    (by simp; omega) i.succ.castSucc (Finset.mem_univ _)
    (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos i)) (Fin.castSucc_lt_last _)

lemma dgCoherentBarFullTerm_eq_composite {n : ℕ} (s : SimplexData R C (n + 1)) (i : Fin n) :
    dgCoherentBarFullTerm s i =
      (((Finset.univ : Finset (Fin (n + 2))).filter (i.succ.castSucc < ·)).card : ℤ).negOnePow •
        (dgCoherentBarFullErase s i - dgCoherentBarFullComposite s i) := rfl

lemma dgCoherentBarHom_unit_heq {a b : C} (h : a = b) :
    HEq (unitElement R a).val (unitElement R b).val := by
  cases h
  rfl

lemma dgCoherentBarHom_compose_degree_heq {a b c : C} {p q k l : ℤ}
    (g : GradedHom R b c q) (f : GradedHom R a b p) (h : p + q = k) (h' : p + q = l) :
    HEq (compose R g f h) (compose R g f h') := by
  have he : k = l := h.symm.trans h'
  cases he
  rfl

end SerrePositivity.InfinityCategories
