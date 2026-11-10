module
public import SerrePositivity.KST.ProExcision.IntegerIntervalWeights
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
# 単体的整数区間から二項鎖区間への比較

概要：ℤΔ¹ の交代面複体を二頂点・一辺の実鎖区間へ送る。
方針：零次は頂点の同定、一次は終点から始点を引いた係数、二次以降は零。
規約：KST Definition A.3、Construction A.5、非被約な零次を保持する。
使われ方：正規化鎖ホモトピーから単体的区間射への復元の中間写像。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite AlgebraicTopology
open scoped Simplicial

/-- 概要：標準区間の単体の指定頂点の値。
方針：標準単体と単体圏の射の同値を評価する。
規約：KST A.3、値は区間の二頂点。
使われ方：区間の鎖比較の成分。 -/
def intervalSimplexVertex {n : ℕ} (x : (Δ[1] : SSet.{u}).obj (op ⦋n⦌))
    (j : Fin (n + 1)) : Fin 2 := (SSet.stdSimplex.objEquiv x).toOrderHom j

/-- 概要：頂点の値は標準単体の単体射による制限と可換。
方針：標準単体の反変な前合成を評価する。
規約：KST A.3。使われ方：区間の微分との可換性。 -/
lemma intervalSimplexVertex_map {n m : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌)
    (x : (Δ[1] : SSet.{u}).obj (op ⦋m⦌)) (j : Fin (n + 1)) :
    intervalSimplexVertex ((Δ[1] : SSet.{u}).map f.op x) j =
      intervalSimplexVertex x (f.toOrderHom j) := rfl

/-- 概要：単体的整数区間から二項鎖区間への比較の次数ごとの写像。
方針：頂点はその値へ送り、辺は両端の差で重みを付け、高次は零にする。
規約：KST A.3・A.5、辺の境界は終点−始点。
使われ方：実鎖写像へ束ねる区間の比較。 -/
def integerIntervalComparisonApp : (n : ℕ) →
    ((alternatingFaceMapComplex _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))).X n ⟶
      integerChainInterval.X n
  | 0 => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map (↾fun x ↦ ULift.up (intervalSimplexVertex x 0))
  | 1 => _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc (fun x ↦
      integerIntervalWeight (intervalSimplexVertex x 0) (intervalSimplexVertex x 1) • integerIntervalEdge)
  | _ + 2 => 0

/-- 概要：区間比較の零次は頂点の基底をその値の基底へ送る。
方針：自由化した写像の基底上の評価。
規約：KST A.3。使われ方：微分の零次と区間の両端。 -/
@[simp] lemma integerIntervalComparisonApp_zero_generator
    (x : (Δ[1] : SSet.{u}).obj (op ⦋0⦌)) :
    integerIntervalComparisonApp 0 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) =
      integerIntervalVertex (intervalSimplexVertex x 0) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator _ x

/-- 概要：区間比較の一次は辺の基底を両端の差の重み付き辺へ送る。
方針：整数線形拡張の基底上の評価。
規約：KST A.3。使われ方：微分の一次・二次の計算。 -/
@[simp] lemma integerIntervalComparisonApp_one_generator
    (x : (Δ[1] : SSet.{u}).obj (op ⦋1⦌)) :
    integerIntervalComparisonApp 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) =
      integerIntervalWeight (intervalSimplexVertex x 0) (intervalSimplexVertex x 1) • integerIntervalEdge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearizationDesc_generator _ x

/-- 概要：区間比較は一次から零次への微分と可換。
方針：辺の境界を両端の差へ同定し、単体の二つの面の値と比較する。
規約：KST A.3・A.5。使われ方：実区間の鎖写像性の一次。 -/
lemma integerIntervalComparison_comm_zero :
    integerIntervalComparisonApp.{u} 1 ≫ integerChainInterval.d 1 0 =
    ((alternatingFaceMapComplex _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))).d 1 0 ≫
      integerIntervalComparisonApp 0 := by
  change integerIntervalComparisonApp 1 ≫ integerIntervalBoundary = _
  rw [alternatingFaceMapComplex_obj_d,
    AlternatingFaceMapComplex.objD, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro x
  change integerIntervalBoundary (integerIntervalComparisonApp 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) =
    integerIntervalComparisonApp 0
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})).δ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) +
        -(((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})).δ 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)))
  rw [map_add, map_neg]
  simp only [← sub_eq_add_neg]
  change integerIntervalBoundary (integerIntervalComparisonApp 1 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) =
    integerIntervalComparisonApp 0
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((Δ[1] : SSet.{u}).δ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) -
    integerIntervalComparisonApp 0
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((Δ[1] : SSet.{u}).δ 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))
  rw [integerIntervalComparisonApp_one_generator, map_smul, integerIntervalBoundary_edge,
    integerIntervalWeight_vertices, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, integerIntervalComparisonApp_zero_generator,
    integerIntervalComparisonApp_zero_generator]
  rfl

/-- 概要：区間比較は二次から一次への微分と可換。
方針：三つの辺の重みの望遠鏡相殺を使う。
規約：KST A.3・A.5。使われ方：実区間の鎖写像性の二次。 -/
lemma integerIntervalComparison_comm_one :
    integerIntervalComparisonApp.{u} 2 ≫ integerChainInterval.d 2 1 =
    ((alternatingFaceMapComplex _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))).d 2 1 ≫
      integerIntervalComparisonApp 1 := by
  have h₂ : integerIntervalComparisonApp.{u} 2 = 0 := rfl
  rw [h₂, Limits.zero_comp, alternatingFaceMapComplex_obj_d,
    AlternatingFaceMapComplex.objD, Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul,
    show (-1 : ℤ) ^ ((2 : Fin 3) : ℕ) = 1 from by decide]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro x
  change 0 = integerIntervalComparisonApp 1
    ((((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})).δ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x) +
      -(((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})).δ 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))) +
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})).δ 2) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))
  rw [map_add, map_add, map_neg]
  simp only [← sub_eq_add_neg]
  change 0 =
    integerIntervalComparisonApp 1
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((Δ[1] : SSet.{u}).δ 0) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) -
    integerIntervalComparisonApp 1
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((Δ[1] : SSet.{u}).δ 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) +
    integerIntervalComparisonApp 1
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((Δ[1] : SSet.{u}).δ 2) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator,
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, integerIntervalComparisonApp_one_generator,
    integerIntervalComparisonApp_one_generator, integerIntervalComparisonApp_one_generator]
  change 0 = integerIntervalWeight (intervalSimplexVertex x 1) (intervalSimplexVertex x 2) •
      integerIntervalEdge -
    integerIntervalWeight (intervalSimplexVertex x 0) (intervalSimplexVertex x 2) • integerIntervalEdge +
    integerIntervalWeight (intervalSimplexVertex x 0) (intervalSimplexVertex x 1) • integerIntervalEdge
  rw [← sub_smul, ← add_smul, integerIntervalWeight_triangle, zero_smul]

/-- 概要：単体的整数区間から二項鎖区間への実鎖写像。
方針：一次・二次の境界公式と高次数の零成分を合成する。
規約：KST Definition A.3、Construction A.5、非被約な頂点を保つ。
使われ方：鎖ホモトピーから単体的テンソル区間写像への復元。 -/
def integerIntervalComparison :
    (alternatingFaceMapComplex _).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})) ⟶ integerChainInterval :=
  ChainComplex.ofHom integerIntervalComparisonApp (fun n ↦ by
    cases n with
    | zero => exact integerIntervalComparison_comm_zero
    | succ n =>
      cases n with
      | zero => exact integerIntervalComparison_comm_one
      | succ n =>
        change (0 : _ ⟶ _) ≫ _ = _ ≫ (0 : _ ⟶ _)
        rw [Limits.zero_comp, Limits.comp_zero])

end SerrePositivity.KST.ProExcision
