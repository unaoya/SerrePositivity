module
public import SerrePositivity.KST.ProExcision.ChainHomotopyCylinder
public import SerrePositivity.KST.ProExcision.IntervalComparisonConstants

/-!
# 復元する区間写像の AW 各項の計算

概要：区間の復元の実鎖写像を AW の切断ごとに分け、定数単体上の正次数の項を消す。
方針：全テンソルの包含の自然性と区間比較の定数単体の計算を使う。
規約：KST Definition A.3、Construction A.5、両端は非被約な頂点。
使われ方：Dold–Kan で復元した区間射の両端の検証。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial
variable {C D : SimplicialObject (ModuleCat.{u} ℤ)} {f g : C ⟶ D}
variable (H : Homotopy ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g))

/-- 概要：区間の実鎖写像の AW の一つの切断に対応する項。
方針：制限項、テンソルした Moore 射影と区間比較、ホモトピー評価を合成する。
規約：KST A.3・A.5。使われ方：端点での全和を切断ごとに評価する。 -/
def cylinderAWTerm (n : ℕ) (i : Fin (n + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensor C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))).obj (op ⦋n⦌) ⟶
      ((normalizedMooreComplex _).obj D).X n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})) n i ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.chainIntegerTensorMap (PInftyToNormalizedMooreComplex C) integerIntervalComparison).f n ≫
      (chainHomotopyInterval H).f n

/-- 概要：復元の区間の鎖写像の成分は AW の各切断項の有限和。
方針：AW の定義の有限和へ後合成を分配する。
規約：KST A.3・A.5。使われ方：定数単体上で最後の項だけを残す。 -/
lemma chainHomotopyCylinderCore_eq_sum (n : ℕ) :
    (chainHomotopyCylinderCore H).f n = ∑ i : Fin (n + 1), cylinderAWTerm H n i := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneyApp C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})) n ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneyApp, Preadditive.sum_comp]
  rfl

/-- 概要：AW の切断項は二つの制限・二つの比較・二重次数の評価の合成。
方針：全テンソルの標準包含でテンソル写像とホモトピー評価を計算する。
規約：KST A.3・A.5。使われ方：各項の純テンソル上の計算。 -/
lemma cylinderAWTerm_eq (n : ℕ) (i : Fin (n + 1)) :
    cylinderAWTerm H n i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap (C.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront n i).op)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack n i).op) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerTensorMap ((PInftyToNormalizedMooreComplex C).f i)
          (integerIntervalComparison.f (n - i)) ≫
            chainHomotopyIntervalBidegree H i (n - i) n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDegrees n i) := by
  rw [cylinderAWTerm, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand, Category.assoc]
  have ht := congrArg (fun k ↦ k ≫ (chainHomotopyInterval H).f n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap (PInftyToNormalizedMooreComplex C) integerIntervalComparison
      i (n - i) n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDegrees n i))
  simp only [Category.assoc] at ht
  erw [ht]
  erw [ι_chainHomotopyIntervalApp]

/-- 概要：最後の切断より前の AW 項は区間の端点の定数単体上で零。
方針：正の区間次数の定数単体は区間比較で零になる。
規約：KST A.3・A.5。使われ方：復元の両端で最後の切断だけを残す。 -/
lemma cylinderAWTerm_constant_of_lt (n : ℕ) (i : Fin (n + 1)) (hi : (i : ℕ) < n)
    (v : C.obj (op ⦋n⦌)) (j : Fin 2) :
    cylinderAWTerm H n i (TensorProduct.tmul ℤ v
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 j (op ⦋n⦌)))) = 0 := by
  rw [cylinderAWTerm_eq]
  change chainHomotopyIntervalBidegree H i (n - i) n (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awDegrees n i)
    (TensorProduct.tmul ℤ
      ((PInftyToNormalizedMooreComplex C).f i (C.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront n i).op v))
      (integerIntervalComparison.f (n - i)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((Δ[1] : SSet.{u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack n i).op)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 j (op ⦋n⦌)))))) = 0
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, intervalConstant_map,
    integerIntervalComparison_constant_of_pos (n - i) (by omega), TensorProduct.tmul_zero, map_zero]

end SerrePositivity.KST.ProExcision
