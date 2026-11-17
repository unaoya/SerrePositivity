module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletionDerived

/-!
# 有限反復完備化の標準単位の冪等性

## 概要
全座標に完備な複体では元の合成単位が同型となり、任意の単位は再完備化後に同型となる。

## 方針
既存の標準単位への前合成の Hom 同値と、その単射性だけで両逆を確認する。

## 規約
対象ごとの任意の同型を完備化の構造として選ばない。

## 使われ方
BS 著者版 Lemma 4.22 の有限頭部で、各行の完備化単位を反転する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]

/-- 全座標に完備な複体では、元の合成単位は導来圏で同型である。 -/
theorem finiteCompletionUnit_isIso_of_isComplete {r : ℕ} (x : Fin r → R) (K : Complex R)
    (hK : ∀ j, IsComplete R (x j) (DerivedCategory.Q.obj K)) :
    IsIso (DerivedCategory.Q.map (finiteCompletionUnit x K)) := by
  let v := (finiteCompletionHomEquiv x K (DerivedCategory.Q.obj K) hK).symm (𝟙 _)
  have huv : DerivedCategory.Q.map (finiteCompletionUnit x K) ≫ v = 𝟙 _ := by
    have h := (finiteCompletionHomEquiv x K (DerivedCategory.Q.obj K) hK).apply_symm_apply (𝟙 _)
    simpa only [finiteCompletionHomEquiv_apply] using h
  refine ⟨⟨v, huv, ?_⟩⟩
  apply finiteCompletionHom_ext x K
    (DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj K)) (finiteCompletion_isComplete x K)
  rw [← Category.assoc, huv, Category.id_comp, Category.comp_id]

/-- 完備化関手を元の単位へ施すと、完備な対象での元の単位と一致する。 -/
theorem finiteCompletion_map_unit {r : ℕ} (x : Fin r → R) (K : Complex R) :
    DerivedCategory.Q.map ((finiteCompletionFunctor x).map (finiteCompletionUnit x K)) =
      DerivedCategory.Q.map (finiteCompletionUnit x ((finiteCompletionFunctor x).obj K)) := by
  apply finiteCompletionHom_ext x K
    (DerivedCategory.Q.obj ((finiteCompletionFunctor x).obj ((finiteCompletionFunctor x).obj K)))
    (finiteCompletion_isComplete x ((finiteCompletionFunctor x).obj K))
  simpa only [Functor.map_comp] using
    (congrArg DerivedCategory.Q.map (finiteCompletionUnit_naturality x (finiteCompletionUnit x K))).symm

/-- 元の有限合成単位は、同じ導来完備化を再度施すと同型となる。 -/
theorem finiteDerivedCompletion_map_unit_isIso {r : ℕ} (x : Fin r → R) (K : Complex R) :
    IsIso ((finiteDerivedCompletionFunctor x).map
      (DerivedCategory.Q.map (finiteCompletionUnit x K))) := by
  apply (NatIso.isIso_map_iff (finiteDerivedCompletionComparison x) (finiteCompletionUnit x K)).mpr
  change IsIso (DerivedCategory.Q.map ((finiteCompletionFunctor x).map (finiteCompletionUnit x K)))
  rw [finiteCompletion_map_unit]
  exact finiteCompletionUnit_isIso_of_isComplete x _ (finiteCompletion_isComplete x K)

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
