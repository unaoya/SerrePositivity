module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletedComparisonIso
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteTruncationTorBounds

/-!
# 完全 Tor 振幅の下での完備テンソルと積全複体の比較

## 概要
一様なコホモロジー下界を持つ非負横次数の図式について、元の標準完備比較は同型となる。

## 方針
各固定次数で十分深い有限頭部を選ぶ。両側の射影の擬同型性と、同じ標準比較の自然性を使う。

## 規約
ここでは指定した R 上の固定 K-flat 係数模型と有限反復完備化の比較を証明する。
標準 S 線形底変換への同定は別途行う。

## 使われ方
BS 著者版 Lemma 4.22 の鎖複体版の固定係数模型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 具体的複体の指定次数の擬同型性は、導来圏の同じホモロジー関手で検出される。 -/
theorem derived_homology_map_isIso_of_quasiIsoAt {K M : Complex R} (g : K ⟶ M) (q : ℤ)
    (hg : QuasiIsoAt g q) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) q).map (DerivedCategory.Q.map g)) := by
  apply (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) q) g).mpr
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp hg

namespace ScalarResolution
variable {f : R →+* S} (L : ScalarResolution f)

/-- 有限完全 Tor 振幅と行の一様下界の下で、指定模型の標準完備比較は同型となる。 -/
theorem finiteCompletedTensorTotalComparison_isIso {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f x c)
    (K : CochainComplex (Complex R) ℕ) (b : ℤ)
    (hK : ∀ n : ℕ, ∀ i : ℤ, i < b → IsZero ((K.X n).homology i)) :
    IsIso (finiteCompletedTensorTotalComparison x L.complex K) := by
  apply (DerivedCategory.isIso_iff (ModuleCat.{u} R) _).mpr
  intro q
  obtain ⟨N, hN⟩ := exists_nat_gt (q+1-b+(c : ℤ))
  have hbound : q+1 < (N : ℤ)+b-(c : ℤ) := by omega
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) q
  have hSrc := L.finiteCompletedTensor_total_projection_quasiIsoAt x c hf K N b hK q hbound
  have hTgt := L.total_finiteCompletedTensor_projection_quasiIsoAt x c hf K N b hK q hbound
  haveI : IsIso (H.map (DerivedCategory.Q.map ((finiteCompletionFunctor x).map
      (cochainTensorMap (𝟙 L.complex) ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
        (RowTruncation.projection K N)))))) :=
    derived_homology_map_isIso_of_quasiIsoAt _ q hSrc
  haveI : IsIso (H.map (DerivedCategory.Q.map ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
      (((finiteCompletionFunctor x).mapHomologicalComplex (.up ℕ)).map
        (((cochainTensorFixedLeft L.complex).mapHomologicalComplex (.up ℕ)).map
          (RowTruncation.projection K N)))))) :=
    derived_homology_map_isIso_of_quasiIsoAt _ q hTgt
  haveI := finiteCompletedTensorTotalComparison_isIso_of_finiteRows x L.complex
    (RowTruncation.head K N) N (RowTruncation.head_isZero K N)
  have hn := congrArg H.map
    (finiteCompletedTensorTotalComparison_naturality x L.complex (RowTruncation.projection K N))
  simp only [Functor.map_comp] at hn
  haveI : IsIso (H.map (finiteCompletedTensorTotalComparison x L.complex K) ≫ H.map
      (DerivedCategory.Q.map ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
        (((finiteCompletionFunctor x).mapHomologicalComplex (.up ℕ)).map
          (((cochainTensorFixedLeft L.complex).mapHomologicalComplex (.up ℕ)).map
            (RowTruncation.projection K N)))))) := by
    rw [hn]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (H.map (finiteCompletedTensorTotalComparison x L.complex K))
    (H.map (DerivedCategory.Q.map ((cochainProductTotalizationFunctor (ModuleCat.{u} R)).map
      (((finiteCompletionFunctor x).mapHomologicalComplex (.up ℕ)).map
        (((cochainTensorFixedLeft L.complex).mapHomologicalComplex (.up ℕ)).map
          (RowTruncation.projection K N))))))

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
