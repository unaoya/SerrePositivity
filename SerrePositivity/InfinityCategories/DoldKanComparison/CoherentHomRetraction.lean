module

public import SerrePositivity.InfinityCategories.DoldKanComparison.MaximumComponentEvaluation
public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentHomEvaluation

/-!
# 標準 Hom からの射と比較射の合成

概要：標準 Hom から coherent pinched Hom に送って比較で戻す合成は恒等射である。
方針：N4 の回収成分を最大頂点の立方体評価へ移し、二つの次数符号を相殺する。
規約：片側の合成の厳密な等式であり、反対側の合成のホモトピーは別途必要。
使われ方：HA 1.3.1.17、Kerodon 2.5.9 の写像空間の比較のホモトピー同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.DoldKanComparison
open CategoryTheory DifferentialGraded
open scoped Simplicial
variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D]

/-- 概要：標準 Hom の単体を coherent pinched 単体にして比較した N4 成分は次数符号倍となる。
方針：成分回収、端点の移送、最大頂点の旗の評価の三つの異種等号を合成する。
規約：全ての非空頂点集合と全ての標準単体に適用する。
使われ方：Kerodon 2.5.9 の標準座標へ戻すときの符号の相殺。 -/
lemma standardCoherentPinchedSimplex_linear_component {x y : ClosedCategory R D} {n : ℕ}
    (σ : StandardSimplex R (D := D) x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : J.Nonempty) (hk : k = 1 - (J.card : ℤ)) :
    (DGNerve.PinchedHom.toLinearData
      ((coherentPinchedComparison (R := R) (D := D) x y).app _
        (standardCoherentPinchedSimplex σ))).component J k hJ hk =
      degreeSign (J.card - 1) • σ.val.component J k hJ hk := by
  apply eq_of_heq
  apply (coherentPinchedComparison_component_heq (standardCoherentPinchedSimplex σ)
    J k hJ hk).trans
  apply (coherentHomComparison_cubeEvaluation_heq σ (J.min' hJ)
    (coherentVertexInterior.{u} (DGNerve.PinchedHom.withLast J)
      (J.min' hJ).castSucc (Fin.last (n + 1))) (descendingEnumeration _)).trans
  exact cubeEvaluation_withLast_maximum σ J k hJ hk

/-- 概要：標準 Hom から coherent pinched Hom に送って標準比較で戻す合成は恒等射である。
方針：全次数の全成分で回収公式を使い、同じ次数符号の二重作用を消す。
規約：単体集合の射の厳密な等式であり、単に π₀ 上の等式ではない。
使われ方：HA 1.3.1.17 の写像空間の比較の片側の逆の性質。 -/
lemma standardHomToCoherentPinched_comp (x y : ClosedCategory R D) :
    standardHomToCoherentPinched (R := R) x y ≫
      coherentPinchedStandardComparison (R := R) (D := D) x y = 𝟙 _ := by
  apply CategoryTheory.NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro σ
  apply ULift.ext
  apply Subtype.ext
  funext j
  rcases j with ⟨⟨J, k⟩, hJ, hk⟩
  change ((coherentPinchedStandardComparison (R := R) (D := D) x y).app _
    (standardCoherentPinchedSimplex σ.down)).down.val.component J k hJ hk =
      σ.down.val.component J k hJ hk
  rw [coherentPinchedStandardComparison_component,
    standardCoherentPinchedSimplex_linear_component]
  exact degreeSign_smul_involutive _ _

end SerrePositivity.InfinityCategories.DoldKanComparison
