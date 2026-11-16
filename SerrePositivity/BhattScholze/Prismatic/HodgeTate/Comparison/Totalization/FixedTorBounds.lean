module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.ResolvedScalarExtension
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.CompletionBounds
public import SerrePositivity.HomologicalAlgebra.CochainCompleteTorAmplitude
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Tower

/-!
# 固定係数模型上での完全 Tor 振幅

## 概要
既存の半自由分解による完全 Tor 振幅を、固定した係数複体とのテンソルへ渡す。

## 方針
証明の中でだけ入力の半自由分解を取り、二つの擬同型と係数制限による Koszul の同型を使う。

## 規約
固定係数模型に標的環の作用を追加しない。入力の平坦性や有界性は要求しない。

## 使われ方
BS 著者版 Lemma 4.22 の完備底変換後の一様なコホモロジーの下界。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 有限 Koszul 関手は非有界複体の擬同型を保つ。 -/
theorem koszulFunctor_map_quasiIso {r : ℕ} (x : Fin r → R)
    {K M : Complex R} (g : K ⟶ M) [QuasiIso g] :
    QuasiIso ((koszulFunctor x).map g) := by
  induction r with
  | zero => exact ‹QuasiIso g›
  | succ r ih =>
    haveI := ih (Fin.init x)
    exact scalarConeFunctor_map_quasiIso R (x (Fin.last r))
      ((koszulFunctor (Fin.init x)).map g)

/-- 係数制限と有限 Koszul の同型。各段は元のスカラー錐の同型である。 -/
def restrictionKoszulIso (f : R →+* S) : ∀ {r : ℕ} (x : Fin r → R) (K : Complex S),
    ((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj
        (koszulComplexOn (f ∘ x) K) ≅
      koszulComplexOn x
        (((ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)).obj K)
  | 0, _, _ => Iso.refl _
  | r + 1, x, K =>
    restrictionScalarConeIso f (x (Fin.last r)) (f (x (Fin.last r))) rfl
      (koszulComplexOn (f ∘ Fin.init x) K) ≪≫
        (scalarConeFunctor (x (Fin.last r))).mapIso (restrictionKoszulIso f (Fin.init x) K)

namespace ScalarResolution

variable {f : R →+* S} (L : ScalarResolution f)

/-- 既存の完全 Tor 振幅は固定係数模型の Koszul ホモロジーにも同じ上界を与える。 -/
theorem koszul_lowerBound {r : ℕ} (x : Fin r → R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f x c) (K : Complex R) (m : ℤ)
    (hK : ∀ i : ℤ, i < m → IsZero (K.homology i))
    (i : ℤ) (hi : i < m - (c : ℤ)) :
    IsZero ((koszulComplexOn x (L.tensorFunctor.obj K)).homology i) := by
  obtain ⟨P, q, hq, hP, hFlat, _, hb⟩ := exists_cochainCompleteTor_model f x c hf K m hK
  haveI : QuasiIso q := hq
  haveI : QuasiIso (L.tensorFunctor.map q) := L.tensorFunctor_map_quasiIso q
  haveI : QuasiIso (L.comparison P) := L.comparison_quasiIso P hFlat
  haveI : QuasiIso ((koszulFunctor x).map (L.tensorFunctor.map q)) :=
    koszulFunctor_map_quasiIso x _
  haveI : QuasiIso ((koszulFunctor x).map (L.comparison P)) :=
    koszulFunctor_map_quasiIso x _
  let Res := ModuleCat.restrictScalars f
  let C := koszulComplexOn (f ∘ x) (baseChange f P)
  have hC : IsZero (Res.obj (C.homology i)) := Res.map_isZero (hb i hi)
  have hRes : IsZero (((Res.mapHomologicalComplex (.up ℤ)).obj C).homology i) :=
    hC.of_iso ((C.sc i).mapHomologyIso Res)
  have hKoszul : IsZero ((koszulComplexOn x
      ((Res.mapHomologicalComplex (.up ℤ)).obj (baseChange f P))).homology i) :=
    hRes.of_iso ((homologyFunctor (ModuleCat.{u} R) (.up ℤ) i).mapIso
      (restrictionKoszulIso f x (baseChange f P))).symm
  have hFixed : IsZero ((koszulComplexOn x (L.tensorFunctor.obj P)).homology i) :=
    hKoszul.of_iso (isoOfQuasiIsoAt ((koszulFunctor x).map (L.comparison P)) i)
  exact hFixed.of_iso (isoOfQuasiIsoAt
    ((koszulFunctor x).map (L.tensorFunctor.map q)) i).symm

/-- 主元の完全 Tor 振幅は、既存の完備化関手の値にも同じ下界を与える。 -/
theorem completedTensor_lowerBound_principal (a : R) (c : ℕ)
    (hf : HasCochainCompleteTorAmplitude f (fun _ : Fin 1 => a) c)
    (K : Complex R) (m : ℤ)
    (hK : ∀ i : ℤ, i < m → IsZero (K.homology i))
    (i : ℤ) (hi : i < m - (c : ℤ)) :
    IsZero (((L.completedTensorFunctor a).obj K).homology i) := by
  apply completion_lowerBound_of_scalarCone a (L.tensorFunctor.obj K) (m - (c : ℤ))
    (fun j hj => ?_) i hi
  exact L.koszul_lowerBound (fun _ : Fin 1 => a) c hf K m hK j hj

end ScalarResolution
end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
