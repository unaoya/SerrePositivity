module

public import SerrePositivity.KST.Spectra.LastVertexKanWeightComparison
public import SerrePositivity.KST.Spectra.CosimplicialTwoProjections
public import SerrePositivity.KST.Spectra.CosimplicialProjectionEquivalence
public import SerrePositivity.KST.Spectra.CosimplicialRelativeWhitehead

/-!
概要：置換した終頂点の射の二射影分解は相対 matching の全単射 RLP を持つ。
方針：実際の各段の π 同型を相対 Whitehead に渡す。
規約：全ての単射への右持ち上げ性を言い、モデル構造を仮定しない。
使われ方：Goerss–Jardine VII §4。cofibrant な重みの図式ホモトピー比較への入力。
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.Reedy
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.CosimplicialLastVertex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Reedy Kan 置換は実際の終射について Reedy fibrant。 -/
lemma replacement_reedyTerminal (X : CosimplicialObject SSet.{u}) :
    reedyRight simplex modelCategoryQuillen.J.rlp
      (terminal.from (CosimplicialKanReplacement.functor.obj X)) := by
  apply (CosimplicialHornFibration.terminal_iff _).mpr
  have he : (CosimplicialKanReplacement.terminalArrows.obj
      (CosimplicialKanReplacement.functor.obj X)).hom =
      CosimplicialHornFactorization.factorization.p.app
        (CosimplicialKanReplacement.terminalArrows.obj X) := by
    apply NatTrans.ext
    funext j
    exact terminal.hom_ext _ _
  rw [he]
  exact CosimplicialKanReplacement.reedy_terminal_rlp X

/-- BK 重みの置換の各段の実際の参照頂点。 -/
def kanWeightVertex (j : SimplexCategory) :
    (CosimplicialKanReplacement.functor.obj BousfieldKanWeightLatching.weight.{u}).obj j _⦋0⦌ :=
  (overTerminalPoint (AsSmall.up.obj j) ≫
    (CosimplicialKanReplacement.unit.app BousfieldKanWeightLatching.weight).app j).app _
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1))

/-- 二射影の source 射影の相対 matching は全ての単射への RLP を持つ。 -/
lemma kanWeightSourceProjection_matching :
    reedyRight simplex (MorphismProperty.monomorphisms SSet.{u}).rlp
      (CosimplicialTwoProjections.sourceProjection kanWeightMap.{u}) := by
  let : ∀ j, KanComplex ((CosimplicialTwoProjections.obj kanWeightMap.{u}).obj j) :=
    fun j ↦ CosimplicialTwoProjections.obj_kanComplex _ (replacement_reedyTerminal _) j
  exact CosimplicialRelativeWhitehead.matching_rlp_of_levelwise _
    (CosimplicialTwoProjections.sourceProjection_reedy _ (replacement_reedyTerminal _))
    (CosimplicialTwoProjections.sourceProjection_levelwise _ kanWeightVertex)
    (fun j ↦ (CosimplicialTwoProjections.inclusion kanWeightMap).app j |>.app _ (kanWeightVertex j))

/-- 二射影の target 射影の相対 matching も全ての単射への RLP を持つ。 -/
lemma kanWeightTargetProjection_matching :
    reedyRight simplex (MorphismProperty.monomorphisms SSet.{u}).rlp
      (CosimplicialTwoProjections.targetProjection kanWeightMap.{u}) := by
  let : ∀ j, KanComplex ((CosimplicialTwoProjections.obj kanWeightMap.{u}).obj j) :=
    fun j ↦ CosimplicialTwoProjections.obj_kanComplex _ (replacement_reedyTerminal _) j
  exact CosimplicialRelativeWhitehead.matching_rlp_of_levelwise _
    (CosimplicialTwoProjections.targetProjection_reedy _ (replacement_reedyTerminal _))
    (CosimplicialTwoProjections.targetProjection_levelwise _
      kanWeightMap_piIsomorphism kanWeightVertex)
    (fun j ↦ (CosimplicialTwoProjections.inclusion kanWeightMap).app j |>.app _ (kanWeightVertex j))

end
end SerrePositivity.KST.Spectra.CosimplicialLastVertex
