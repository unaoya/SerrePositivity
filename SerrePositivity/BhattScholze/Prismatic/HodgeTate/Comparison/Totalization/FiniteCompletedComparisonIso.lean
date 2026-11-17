module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletedComparison
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionIdempotent
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteRowEquivalence
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteTensorComparisonIso

/-!
# 有限頭部での標準完備テンソル比較の同型性

## 概要
有限横行では、元の標準比較を有限列で完備化した射が同型になる。

## 方針
完備化前のテンソル比較は鎖同型であり、各行の元の単位は再完備化で同型となる。
有限行の完全三角形の帰納と、標準単位での射の一意性を使う。

## 規約
内部次数に項ごとの有界性を課さず、比較の可逆性を外部の仮定にしない。

## 使われ方
BS 著者版 Lemma 4.22 の有限頭部の場合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion
open SerrePositivity.HomologicalAlgebra

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- 完備比較に標的の元の単位を合成すると、元の比較の完備化になる。 -/
@[reassoc] theorem finiteCompletedTensorTotalComparison_comp_unit
    {r : ℕ} (x : Fin r → R) (L : Complex R) (K : CochainComplex (Complex R) ℕ) :
    finiteCompletedTensorTotalComparison x L K ≫ DerivedCategory.Q.map
        (finiteCompletionUnit x (total (finiteCompletedRows x (tensorRows L K)))) =
      DerivedCategory.Q.map ((finiteCompletionFunctor x).map (tensorToFiniteCompletedRows x L K)) := by
  apply finiteCompletionHom_ext x (cochainTensor L (total K))
    (DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj
      (total (finiteCompletedRows x (tensorRows L K)))))
    (finiteCompletion_isComplete x (total (finiteCompletedRows x (tensorRows L K))))
  rw [unit_comp_finiteCompletedTensorTotalComparison_assoc]
  simpa only [Functor.map_comp] using congrArg DerivedCategory.Q.map
    (finiteCompletionUnit_naturality x (tensorToFiniteCompletedRows x L K))

/-- 有限横行の各行の標準完備化単位は、Tot の後で再完備化しても同型になる。 -/
theorem finiteDerivedCompletion_total_rowsUnit_isIso {r : ℕ} (x : Fin r → R)
    (K : CochainComplex (Complex R) ℕ) (N : ℕ)
    (hK : ∀ n : ℕ, N ≤ n → IsZero (K.X n)) :
    IsIso ((finiteDerivedCompletionFunctor x).map (DerivedCategory.Q.map
      ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map (finiteCompletionRowsUnit x K)))) := by
  apply isIso_map_total_of_finite_rows (finiteDerivedCompletionFunctor x) N
    (finiteCompletionRowsUnit x K) hK
  · intro n hn
    exact (finiteCompletionFunctor x).map_isZero (hK n hn)
  · intro n
    exact finiteDerivedCompletion_map_unit_isIso x (K.X n)

/-- 有限横行では、同じ元の標準完備比較が導来圏で同型となる。 -/
theorem finiteCompletedTensorTotalComparison_isIso_of_finiteRows
    {r : ℕ} (x : Fin r → R) (L : Complex R)
    (K : CochainComplex (Complex R) ℕ) (N : ℕ)
    (hK : ∀ n : ℕ, N ≤ n → IsZero (K.X n)) :
    IsIso (finiteCompletedTensorTotalComparison x L K) := by
  haveI := tensorTotalComparison_isIso_of_finiteRows L K N hK
  haveI := finiteDerivedCompletion_total_rowsUnit_isIso x (tensorRows L K) N
    (fun n hn => (cochainTensorFixedLeft L).map_isZero (hK n hn))
  have hRaw : IsIso ((finiteDerivedCompletionFunctor x).map
      (DerivedCategory.Q.map (tensorToFiniteCompletedRows x L K))) := by
    dsimp only [tensorToFiniteCompletedRows]
    rw [Functor.map_comp, Functor.map_comp]
    infer_instance
  haveI : IsIso (DerivedCategory.Q.map
      ((finiteCompletionFunctor x).map (tensorToFiniteCompletedRows x L K))) :=
    (NatIso.isIso_map_iff (finiteDerivedCompletionComparison x)
      (tensorToFiniteCompletedRows x L K)).mp hRaw
  haveI := finiteCompletionUnit_isIso_of_isComplete x
    (total (finiteCompletedRows x (tensorRows L K)))
    (total_finiteCompletedRows_isComplete x (tensorRows L K))
  haveI : IsIso (finiteCompletedTensorTotalComparison x L K ≫ DerivedCategory.Q.map
      (finiteCompletionUnit x (total (finiteCompletedRows x (tensorRows L K))))) := by
    rw [finiteCompletedTensorTotalComparison_comp_unit]
    infer_instance
  exact IsIso.of_isIso_comp_right (finiteCompletedTensorTotalComparison x L K)
    (DerivedCategory.Q.map (finiteCompletionUnit x (total (finiteCompletedRows x (tensorRows L K)))))

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
