module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteCompletion
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.KoszulScalarNaturality

/-!
# 有限列の反復完備化の標準単位と下界

## 概要
反復した元の単位の有限 Koszul 簡約を擬同型とし、同じ Koszul 下界を完備化へ渡す。

## 方針
末尾の単位にはスカラー錐と残りの Koszul の自然な交換を使い、列の長さで帰納する。

## 規約
元の合成単位を使い、列長を下界から二重に差し引かない。

## 使われ方
BS 著者版 Lemma 4.22 の有限生成イデアルの完備底変換の一様な下界。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
attribute [local instance] HasDerivedCategory.standard
variable {R S : Type u} [CommRing R] [CommRing S]

/-- 末尾の主元の標準完備化単位は、列全体の Koszul で簡約すると擬同型である。 -/
theorem koszul_last_completionUnit_quasiIso {r : ℕ} (x : Fin (r+1) → R) (K : Complex R) :
    QuasiIso ((koszulFunctor x).map (complexCompletionUnit R (x (Fin.last r)) K)) := by
  let a := x (Fin.last r)
  let y := Fin.init x
  let C := complexCompletionFunctor R a
  let u := complexCompletionUnit R a K
  haveI : QuasiIso ((scalarConeFunctor a).map u) := by
    change QuasiIso ((scalarConeFunctor a).map (complexCompletionUnit R a K))
    have h := complexCompletionUnit_koszul_quasiIso R a K 1
    rw [pow_one] at h
    exact h
  haveI : QuasiIso ((koszulFunctor y).map ((scalarConeFunctor a).map u)) :=
    koszulFunctor_map_quasiIso y _
  let e := scalarConeKoszulNatIso a y
  have hn := e.hom.naturality u
  change (scalarConeFunctor a).map ((koszulFunctor y).map u) ≫ e.hom.app (C.obj K) =
    e.hom.app K ≫ (koszulFunctor y).map ((scalarConeFunctor a).map u) at hn
  have hc : QuasiIso ((scalarConeFunctor a).map ((koszulFunctor y).map u) ≫
      e.hom.app (C.obj K)) := by
    rw [hn]
    infer_instance
  exact (quasiIso_iff_comp_right _ _).mp hc

/-- 反復した元の標準単位は、有限 Koszul の簡約で擬同型になる。 -/
theorem finiteCompletionUnit_koszul_quasiIso {r : ℕ} (x : Fin r → R) (K : Complex R) :
    QuasiIso ((koszulFunctor x).map (finiteCompletionUnit x K)) := by
  induction r with
  | zero => change QuasiIso (𝟙 K); infer_instance
  | succ r ih =>
    haveI := ih (Fin.init x)
    haveI : QuasiIso ((koszulFunctor x).map (finiteCompletionUnit (Fin.init x) K)) :=
      scalarConeFunctor_map_quasiIso R (x (Fin.last r))
        ((koszulFunctor (Fin.init x)).map (finiteCompletionUnit (Fin.init x) K))
    haveI := koszul_last_completionUnit_quasiIso x ((finiteCompletionFunctor (Fin.init x)).obj K)
    change QuasiIso ((koszulFunctor x).map (finiteCompletionUnit (Fin.init x) K ≫
      complexCompletionUnit R (x (Fin.last r)) ((finiteCompletionFunctor (Fin.init x)).obj K)))
    rw [Functor.map_comp]
    infer_instance

/-- 元の有限 Koszul 下界は、同じ値で反復完備化の下界になる。 -/
theorem finiteCompletion_lowerBound {r : ℕ} (x : Fin r → R) (K : Complex R) (b : ℤ)
    (hK : ∀ i : ℤ, i < b → IsZero ((koszulComplexOn x K).homology i))
    (i : ℤ) (hi : i < b) :
    IsZero (((finiteCompletionFunctor x).obj K).homology i) := by
  haveI := finiteCompletionUnit_koszul_quasiIso x K
  have hz : IsZero ((koszulComplexOn x ((finiteCompletionFunctor x).obj K)).homology i) :=
    (hK i hi).of_iso (isoOfQuasiIsoAt ((koszulFunctor x).map (finiteCompletionUnit x K)) i).symm
  exact homology_isZero_of_finitelyComplete_koszul x _ (finiteCompletion_isComplete x K) i hz

namespace ScalarResolution
variable {f : R →+* S} (L : ScalarResolution f)

/-- 同じ固定係数テンソルと、元の主元完備化の有限反復。 -/
abbrev finiteCompletedTensorFunctor {r : ℕ} (x : Fin r → R) : Complex R ⥤ Complex R :=
  L.tensorFunctor ⋙ finiteCompletionFunctor x

/-- 有限完全 Tor 振幅から、実際の有限反復完備テンソルの同じ下界を得る。 -/
theorem finiteCompletedTensor_lowerBound {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f x c) (K : Complex R) (m : ℤ)
    (hK : ∀ j : ℤ, j < m → IsZero (K.homology j)) (i : ℤ) (hi : i < m-(c : ℤ)) :
    IsZero (((L.finiteCompletedTensorFunctor x).obj K).homology i) :=
  finiteCompletion_lowerBound x (L.tensorFunctor.obj K) (m-(c : ℤ))
    (fun j hj => L.koszul_lowerBound x c hf K m hK j hj) i hi

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
