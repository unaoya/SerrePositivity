module
public import SerrePositivity.KST.ProExcision.CylinderAWTerms
public import SerrePositivity.KST.ProExcision.LinearizedEndpoints

/-!
# 単体的区間の復元の AW の端点計算

概要：区間の端点では AW の最後の切断だけが残り、指定した端点写像を得る。
方針：正の区間次数の項の零性、最後の切断の計算、有限和の分離を使う。
規約：KST Definition A.3、Construction A.5、両端は非被約な頂点。
使われ方：Dold–Kan による実区間射の両端条件。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial
variable {C D : SimplicialObject (ModuleCat.{u} ℤ)} {f g : C ⟶ D}
variable (H : Homotopy ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g))

/-- 概要：AW の最後の切断の第一因子は全単体の恒等制限。
方針：頂点への評価で比較する。
規約：KST A.5。使われ方：端点で残る最後の AW 項。 -/
lemma awFront_last (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront n (Fin.last n) = 𝟙 ⦋n⦌ := by
  apply SimplexCategory.Hom.ext
  ext j
  rfl

/-- 概要：区間の定数単体上で最後の AW 項は端点の評価に一致。
方針：第一因子の恒等制限と区間比較の零次の計算を使う。
規約：KST A.3・A.5。使われ方：区間復元の両端の全和の値。 -/
lemma cylinderAWTerm_constant_last (n : ℕ) (v : C.obj (op ⦋n⦌)) (j : Fin 2) :
    cylinderAWTerm H n (Fin.last n) (TensorProduct.tmul ℤ v
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 j (op ⦋n⦌)))) =
    chainIntervalEndpointEval (((normalizedMooreComplex _).map f).f n)
      (((normalizedMooreComplex _).map g).f n)
      (TensorProduct.tmul ℤ ((PInftyToNormalizedMooreComplex C).f n v) (integerIntervalVertex j)) := by
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.alexanderWhitneySummand C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})) n (Fin.last n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront n (Fin.last n))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval n 0 n (by omega)) rfl := by
    calc
      _ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront n (Fin.last n))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval n (n - n) n (by omega)) (by omega) := by
        change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront n (Fin.last n))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack n (Fin.last n)) _ = _
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awBack_eq_interval]
        rfl
      _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm_interval_congr C (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront n (Fin.last n)) (Nat.sub_self n) (by omega) (by omega) (by omega) rfl
  rw [cylinderAWTerm, ht, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awTensorTerm, Category.assoc]
  have hp := congrArg (fun k ↦ k ≫ (chainHomotopyInterval H).f n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ι_chainIntegerTensorMap (PInftyToNormalizedMooreComplex C) integerIntervalComparison
      n 0 n rfl)
  simp only [Category.assoc] at hp
  erw [hp, ι_chainHomotopyIntervalApp]
  change chainIntervalEndpointEval (((normalizedMooreComplex _).map f).f n)
      (((normalizedMooreComplex _).map g).f n)
    (TensorProduct.tmul ℤ
      ((PInftyToNormalizedMooreComplex C).f n (C.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront n (Fin.last n)).op v))
      (integerIntervalComparison.f 0
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization.map ((Δ[1] : SSet.{u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awInterval n 0 n (by omega)).op)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 j (op ⦋n⦌)))))) = _
  have hm : C.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.awFront n (Fin.last n)).op = 𝟙 (C.obj (op ⦋n⦌)) := by
    rw [awFront_last]
    exact C.map_id (op ⦋n⦌)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_map_generator, intervalConstant_map,
    integerIntervalComparison_constant_zero]
  erw [hm]
  rfl

/-- 概要：区間の定数単体上の全 AW 比較は対応する頂点の評価。
方針：正次数の項を零にし、最後の切断の項を残す。
規約：KST A.3・A.5、全次数で成立。
使われ方：区間の実鎖写像の端点計算。 -/
lemma chainHomotopyCylinderCore_constant (n : ℕ) (v : C.obj (op ⦋n⦌)) (j : Fin 2) :
    (chainHomotopyCylinderCore H).f n (TensorProduct.tmul ℤ v
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 j (op ⦋n⦌)))) =
    chainIntervalEndpointEval (((normalizedMooreComplex _).map f).f n)
      (((normalizedMooreComplex _).map g).f n)
      (TensorProduct.tmul ℤ ((PInftyToNormalizedMooreComplex C).f n v) (integerIntervalVertex j)) := by
  rw [chainHomotopyCylinderCore_eq_sum]
  change (∑ i : Fin (n + 1), cylinderAWTerm H n i).hom
    (TensorProduct.tmul ℤ v (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 j (op ⦋n⦌)))) = _
  rw [ModuleCat.hom_sum, LinearMap.sum_apply]
  calc
    _ = cylinderAWTerm H n (Fin.last n)
        (TensorProduct.tmul ℤ v (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 j (op ⦋n⦌)))) := by
      apply Finset.sum_eq_single_of_mem (s := Finset.univ)
        (f := fun i : Fin (n + 1) ↦ (cylinderAWTerm H n i).hom
          (TensorProduct.tmul ℤ v (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator (SSet.stdSimplex.const 1 j (op ⦋n⦌)))))
        (Fin.last n) (Finset.mem_univ (Fin.last n))
      intro i _ hi
      have hn : (i : ℕ) ≠ n := fun h ↦ hi (Fin.ext h)
      exact cylinderAWTerm_constant_of_lt H n i (by have := i.isLt; omega) v j
    _ = _ := cylinderAWTerm_constant_last H n v j

/-- 概要：正規化前の鎖区間射の始点は Moore 射影の後の指定始点写像。
方針：自由基底上で零端点の公式と定数単体の全 AW 比較を使う。
規約：KST A.3・A.5。使われ方：正規化後の区間の始点条件。 -/
lemma chainHomotopyCylinderCore_endpoint₀ {X : SSet.{u}}
    {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ D}
    (H : Homotopy ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g)) :
    (alternatingFaceMapComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ X) ≫ chainHomotopyCylinderCore H =
      PInftyToNormalizedMooreComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) ≫ (normalizedMooreComplex _).map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro x
  change (chainHomotopyCylinderCore H).f n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₀ X).app (op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) = _
  rw [linearizedEndpoint₀_generator, chainHomotopyCylinderCore_constant, chainIntervalEndpointEval_zero]
  rfl

/-- 概要：正規化前の鎖区間射の終点は Moore 射影の後の指定終点写像。
方針：自由基底上で一端点の公式と定数単体の全 AW 比較を使う。
規約：KST A.3・A.5。使われ方：正規化後の区間の終点条件。 -/
lemma chainHomotopyCylinderCore_endpoint₁ {X : SSet.{u}}
    {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ D}
    (H : Homotopy ((normalizedMooreComplex _).map f) ((normalizedMooreComplex _).map g)) :
    (alternatingFaceMapComplex _).map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ X) ≫ chainHomotopyCylinderCore H =
      PInftyToNormalizedMooreComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X) ≫ (normalizedMooreComplex _).map g := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerLinearization_hom_ext
  intro x
  change (chainHomotopyCylinderCore H).f n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedEndpoint₁ X).app (op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.integerGenerator x)) = _
  rw [linearizedEndpoint₁_generator, chainHomotopyCylinderCore_constant, chainIntervalEndpointEval_one]
  rfl

end SerrePositivity.KST.ProExcision
