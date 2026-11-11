module
public import SerrePositivity.HomotopicalAlgebra.Simplicial.Generators

public import SerrePositivity.KST.Spectra.CosimplicialHornFactorization
public import SerrePositivity.KST.Spectra.AcyclicFibrationLifting

/-!
概要：余単体 Kan 図式の Reedy fibration に対する相対 Whitehead。
方針：低次数の相対 matching の全ての単射に対する RLP を matching 対象へ送り、次数帰納する。
規約：各段の始域の頂点を明示し、空な始域での条件の空虚性を避ける。
使われ方：Goerss–Jardine VII §4、VIII §1。通常の Tot の π_* 比較。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra SSet SSet.modelCategoryQuillen
open SerrePositivity.Reedy
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.CosimplicialRelativeWhitehead

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：境界の小対象論法は単射と全ての単射に対する RLP の弱因子分解系を与える。
方針：境界から生成する左類が実際の単射に等しいことを使う。
規約：Kan–Quillen モデル構造は不要。
使われ方：Goerss–Jardine VII §4。matching の右類閉性。 -/
lemma boundaryWeakFactorization : MorphismProperty.IsWeakFactorizationSystem
    (MorphismProperty.monomorphisms SSet.{u})
    (MorphismProperty.monomorphisms SSet.{u}).rlp := by
  let : I.{u}.HasSmallObjectArgument.{u} :=
    SerrePositivity.SimplicialModel.boundaryGenerators_smallObjectArgument
  rw [← SerrePositivity.SimplicialModel.boundaryGenerators_leftClass,
    MorphismProperty.rlp_llp_rlp]
  infer_instance

/-- 概要：各段の全基点 π_* 同型である Reedy fibration は相対 matching 全ての単射に対する RLP。
方針：matching に関する右類閉性と本レーンの Kan fibration の Whitehead を次数帰納で使う。
規約：始域の各段に実際の頂点を指定する。
使われ方：Goerss–Jardine VII §4、VIII §1。Tot の比較射を全ての単射に対する RLP で検出する。 -/
lemma matching_rlp_of_levelwise
    {X Y : CosimplicialObject SSet.{u}}
    [∀ j, KanComplex (X.obj j)] [∀ j, KanComplex (Y.obj j)]
    (f : X ⟶ Y) (hf : reedyRight simplex J.rlp f)
    (hπ : ∀ j, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f.app j)) (e₀ : ∀ j, X.obj j _⦋0⦌) :
    reedyRight simplex (MorphismProperty.monomorphisms SSet.{u}).rlp f := by
  let := boundaryWeakFactorization.{u}
  have aux (n : ℕ) : ∀ j : SimplexCategory, j.len = n →
      (MorphismProperty.monomorphisms SSet.{u}).rlp (relativeMatchingMap simplex j f) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro j hj
      let : KanComplex (((evaluation SimplexCategory SSet.{u}).obj j).obj Y) :=
        inferInstanceAs (KanComplex (Y.obj j))
      have hM := matchingEvaluation_mem_right simplex j f
        (MorphismProperty.monomorphisms SSet.{u})
        (MorphismProperty.monomorphisms SSet.{u}).rlp (fun g ↦
          ih g.obj.right.len (hj ▸ matching_degree_lt simplex g) g.obj.right rfl)
      let p := pullback.fst ((matchingComparison simplex j).app Y)
        ((matchingEvaluation simplex j).map f)
      have hp : (MorphismProperty.monomorphisms SSet.{u}).rlp p :=
        (MorphismProperty.monomorphisms SSet.{u}).rlp.pullback_fst _ _ hM
      let : Fibration p := (modelCategoryQuillen.fibration_iff p).mpr
        (fun _ _ a ha ↦ hp a (J_le_monomorphisms a ha))
      let : KanComplex (pullback ((matchingComparison simplex j).app Y)
          ((matchingEvaluation simplex j).map f)) := isFibrant_of_fibration p
      have hpπ := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_monoRight p hp
      let q := relativeMatchingMap simplex j f
      let : Fibration q := (modelCategoryQuillen.fibration_iff q).mpr (hf j)
      have hqp : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (q ≫ p) := by
        change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (relativeMatchingMap simplex j f ≫
          pullback.fst ((matchingComparison simplex j).app Y)
            ((matchingEvaluation simplex j).map f))
        rw [relativeMatchingMap_fst]
        exact hπ j
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fibration_rlp_of_piIsomorphism q (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp hqp hpπ) (e₀ j)
  intro j
  exact aux j.len j rfl

end

end SerrePositivity.KST.Spectra.CosimplicialRelativeWhitehead
