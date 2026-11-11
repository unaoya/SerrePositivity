module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentSimplexTerm

/-!
# 比較成分族の dg 単体の方程式

概要：各 coherent 単体の比較成分族は、既存 dg nerve の全ての有限頂点集合の方程式を満たす。
方針：内部座標の微分公式を頂点番号の和へ移し、既存 rhs の各項へ同定する。
規約：ここでは各次数の dg 単体を構成する。単体的自然性は後続で証明する。
使われ方：HA Construction 1.3.1.16、Kerodon 2.5.9（Tag 00SC） の比較写像の各次数の値。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory CategoryTheory.SimplicialThickening DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：比較単体データの全ての成分は既存 dg nerve の微分方程式を満たす。
方針：両端の間の有限内部点の微分公式を使い、頂点の和と rhs の一項の式へ移す。
規約：始次数は 2−|I| で、削除と合成の式は既存 SimplexData.rhs そのもの。
使われ方：HA 1.3.1.16 の coherent 単体から実際の dg 単体を作る証明。 -/
lemma coherentSimplexData_equation {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌)
    (I : Finset (Fin (n + 1))) (a b : Fin (n + 1)) (k : ℤ)
    (hI : 2 ≤ I.card) (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))
    (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) (hk : k = 2 - (I.card : ℤ)) :
    differential R ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData s).hom I a b k hI ha hb hk) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData s).rhs I a b k hI ha hb hk := by
  have hmin : IsLeast (I : Set (Fin (n + 1))) a := by rw [ha]; exact I.isLeast_min' _
  have hmax : IsGreatest (I : Set (Fin (n + 1))) b := by rw [hb]; exact I.isGreatest_max' _
  have hab : a < b := by rw [ha, hb]; exact I.min'_lt_max'_of_card (by omega)
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} I a b
  have hcard : S.card + 2 = I.card := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior_card hmin hmax hab
  have hdeg : k = -(S.card : ℤ) := by omega
  refine (congrArg (fun f : GradedHom R (s.obj (.mk (ULift.up a)))
    (s.obj (.mk (ULift.up b))) k ↦ differential R f)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData_hom_eq_componentAt s I a b k hI ha hb hk hab hdeg)).trans ?_
  refine (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt_d s (show ULift.up a < ULift.up b from hab)
    S k (k + 1) hdeg rfl).trans ?_
  let F (t : S) := (-1 : ℤ) ^ (S.filter (t.val < ·)).card •
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeCompositionAt s (show ULift.up a < ULift.up b from hab)
      S t (k + 1) (by omega) -
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt s (show ULift.up a < ULift.up b from hab)
        (S.erase t.val) (k + 1) (by have h := Finset.card_erase_add_one t.property; omega))
  refine Eq.trans ?_ ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentInteriorVertex_sum I a b F).trans ?_)
  · apply Finset.sum_congr rfl
    intro t _
    dsimp only [F]
    apply congrArg (fun v ↦ (-1 : ℤ) ^ (S.filter (t.val < ·)).card •
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeCompositionAt s (show ULift.up a < ULift.up b from hab)
        S t (k + 1) (by omega) - v))
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentCubeComponentAt_eq_of_set_eq
    ext x
    simp only [Finset.mem_erase]
  · unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.rhs
    apply Finset.sum_congr rfl
    intro j _
    split_ifs with h
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData_term_eq_interior s I a b k hI ha hb hk hdeg
        j.val j.property h.1 h.2).symm
    · rfl

/-- 概要：coherent 単体を同じ次元の実際の dg 単体へ送る。
方針：頂点と立方体評価の成分族に全ての dg 方程式の証明を付加する。
規約：単体集合の射としての自然性はこの定義の一部ではない。
使われ方：HA 1.3.1.16 の比較写像の各次数の写像。 -/
def coherentSimplex {n : ℕ} (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.doldKanCoherentNerve (R := R) (D := D)) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R D n where
  toSimplexData := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentSimplexData s
  equation := coherentSimplexData_equation s

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
