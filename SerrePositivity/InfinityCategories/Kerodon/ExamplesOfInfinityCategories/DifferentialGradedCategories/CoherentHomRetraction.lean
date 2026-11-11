module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MaximumComponentEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.CoherentHomEvaluation

/-!
# 標準 Hom からの射と比較射の合成

概要：標準 Hom から coherent pinched Hom に送って比較で戻す合成は恒等射である。
方針：N4 の回収成分を最大頂点の立方体評価へ移し、二つの次数符号を相殺する。
規約：片側の合成の厳密な等式であり、反対側の合成のホモトピーは別途必要。
使われ方：HA 1.3.1.17、Kerodon 2.5.9（Tag 00SC） の写像空間の比較のホモトピー同値。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：標準 Hom の単体を coherent pinched 単体にして比較した N4 成分は次数符号倍となる。
方針：成分回収、端点の移送、最大頂点の旗の評価の三つの異種等号を合成する。
規約：全ての非空頂点集合と全ての標準単体に適用する。
使われ方：Kerodon 2.5.9（Tag 00SC） の標準座標へ戻すときの符号の相殺。 -/
lemma standardCoherentPinchedSimplex_linear_component {x y : ClosedCategory R D} {n : ℕ}
    (σ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.StandardSimplex R (D := D) x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedComparison (R := R) (D := D) x y).app _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardCoherentPinchedSimplex σ))).component J k hJ hk =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign (J.card - 1) • σ.val.component J k hJ hk := by
  apply eq_of_heq
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedComparison_component_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardCoherentPinchedSimplex σ)
    J k hJ hk).trans
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentHomComparison_cubeEvaluation_heq σ (J.min' hJ)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentVertexInterior.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withLast J)
      (J.min' hJ).castSucc (Fin.last (n + 1))) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.descendingEnumeration _)).trans
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.cubeEvaluation_withLast_maximum σ J k hJ hk

/-- 概要：標準 Hom から coherent pinched Hom に送って標準比較で戻す合成は恒等射である。
方針：全次数の全成分で回収公式を使い、同じ次数符号の二重作用を消す。
規約：単体集合の射の厳密な等式であり、単に π₀ 上の等式ではない。
使われ方：HA 1.3.1.17 の写像空間の比較の片側の逆の性質。 -/
lemma standardHomToCoherentPinched_comp (x y : ClosedCategory R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardHomToCoherentPinched (R := R) x y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedStandardComparison (R := R) (D := D) x y = 𝟙 _ := by
  apply CategoryTheory.NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro σ
  apply ULift.ext
  apply Subtype.ext
  funext j
  rcases j with ⟨⟨J, k⟩, hJ, hk⟩
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedStandardComparison (R := R) (D := D) x y).app _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.standardCoherentPinchedSimplex σ.down)).down.val.component J k hJ hk =
      σ.down.val.component J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.coherentPinchedStandardComparison_component,
    standardCoherentPinchedSimplex_linear_component]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.degreeSign_smul_involutive _ _

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
