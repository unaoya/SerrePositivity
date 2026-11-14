module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.HomotopicalAlgebra.Simplicial.GeneratedLeftClass
public import SerrePositivity.HomotopicalAlgebra.Smith.Smallness
public import SerrePositivity.HomotopicalAlgebra.Smith.CoproductClosure

/-! # Small generated lifting classes inside a closed class

No accessibility of the ambient morphism class is required. Only the
chosen small generating family needs the small-object argument.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.Smith
variable {C : Type u} [Category.{v} C] (G P : MorphismProperty C)

lemma generatedLeft_le_of_closed [G.HasSmallObjectArgument.{w}]
    [P.IsStableUnderRetracts] [P.IsStableUnderCoproducts.{w}]
    [P.IsStableUnderCobaseChange] [P.IsStableUnderTransfiniteComposition.{w}]
    (hG : G ≤ P) : G.rlp.llp ≤ P := by
  apply ModelGeneration.generatedLeft_le_of_cells_le G P
  apply le_trans (MorphismProperty.transfiniteCompositions_monotone ?_) P.transfiniteCompositions_le
  apply le_trans (MorphismProperty.pushouts_monotone ?_) P.pushouts_le
  exact (MorphismProperty.coproducts_monotone hG).trans P.coproducts_le

end SerrePositivity.Smith

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "A.1.2.5" (partial := stronger-hyp) "仮定：原典の C に加え Mathlib IsLocallyPresentable C、局所小性と一つの colimit universe を明示し、生成射の類は小さい（Lean の形式的仮定が強い）。結論：I.rlp.llp と I.rlp の同じ functorial factorization があり、生成射の両端が κ-presentable なら指定分解の全 arrow factors が κ-filtered colimits を保つ。generatedLeft_le_of_closed と coproduct closure により左類は最小の弱飽和類に入り、原典の二結論に一致。この Mathlib presentability と原典の poset 型定義の完全な比較は含まない。"] _root_.SerrePositivity.Smith.generatedLeft_le_of_closed
attribute [cite HTT "A.1.2.7" (partial := stronger-hyp) "仮定：小さい生成射の類 I、C は Mathlib IsLocallyPresentable（Lean の形式的仮定が強い）。結論：I⊆I.rlp.llp、任意の weakly saturated P⊇I に I.rlp.llp⊆P となり、原典の最小性に一致。I.rlp.llp の三閉性は ordinary lifting-class の既存 instances で与えられる。HTT の presentable の四条件からの比較は別途必要。"] _root_.SerrePositivity.Smith.generatedLeft_le_of_closed
