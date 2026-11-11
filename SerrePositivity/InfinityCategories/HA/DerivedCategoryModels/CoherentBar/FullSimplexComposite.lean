module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.FullSimplexComponents
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
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open CategoryTheory DifferentialGraded
variable {R : Type u} [CommRing R] {C : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]

def dgCoherentBarFullComposite {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C (n + 1)) (i : Fin n) :=
  s.cutComposite Finset.univ 0 (Fin.last (n + 1)) (-(n : ℤ))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_card n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_min n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentDiagramTop_max n)
    (by simp; omega) i.succ.castSucc (Finset.mem_univ _)
    (Fin.castSucc_lt_castSucc_iff.mpr (Fin.succ_pos i)) (Fin.castSucc_lt_last _)

lemma dgCoherentBarFullTerm_eq_composite {n : ℕ} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData R C (n + 1)) (i : Fin n) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullTerm s i =
      (((Finset.univ : Finset (Fin (n + 2))).filter (i.succ.castSucc < ·)).card : ℤ).negOnePow •
        (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.dgCoherentBarFullErase s i - dgCoherentBarFullComposite s i) := rfl

lemma dgCoherentBarHom_unit_heq {a b : C} (h : a = b) :
    HEq (_root_.SerrePositivity.DifferentialGraded.unitElement R a).val (_root_.SerrePositivity.DifferentialGraded.unitElement R b).val := by
  cases h
  rfl

lemma dgCoherentBarHom_compose_degree_heq {a b c : C} {p q k l : ℤ}
    (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R b c q) (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R a b p) (h : p + q = k) (h' : p + q = l) :
    HEq (_root_.SerrePositivity.DifferentialGraded.compose R g f h) (_root_.SerrePositivity.DifferentialGraded.compose R g f h') := by
  have he : k = l := h.symm.trans h'
  cases he
  rfl

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
