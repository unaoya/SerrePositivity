module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoverPairTor
public import SerrePositivity.HomologicalAlgebra.ScalarConeQuotientModel
public import SerrePositivity.HomologicalAlgebra.CochainCompleteTorAmplitude
public import SerrePositivity.HomologicalAlgebra.TwoCoordinateCompleteTor

/-!
# 結晶被覆の完全 Tor 上界三

## 概要
任意の非有界複体の半自由分解上で、結晶被覆の完全 Koszul 模型の下界を評価する。

## 方針
A 上の mod p の振幅二を使い、標的の正則な p のスカラー錐を実際の剰余に比較する。
残る生成元のスカラー錐は下界を高々一だけ下げる。

## 規約
BS 著者版 Construction 6.1、Construction 6.1 の Tor 振幅 の上界三。通常の mod p の上界一と区別する。

## 使われ方
Lemma 4.22 の古典的な有限振幅の入力。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity.BhattScholze.Prismatic.Construction61
open CategoryTheory CategoryTheory.Limits DifferentialGraded DerivedCompletion InfinityCategories

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- 概要：結晶被覆の標準射は完全 Tor 振幅の上界三を持つ。
方針：実際の分解上で p の Koszul 因子を通常の mod p に比較し、振幅二と残りの錐を使う。
規約：BS 著者版 Construction 6.1、Construction 6.1 の Tor 振幅。全ての非有界な半自由分解を検査する。
使われ方：Tot と底変換の比較に渡す古典的な有限振幅。 -/
theorem crystallineCoverMap_torAmplitude
    (hF : IsCompletelyFlat (Ideal.span {coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    HasCochainCompleteTorAmplitude (crystallineCoverMap P).toRingHom ![(p : A), P.generator] 3 := by
  let B := crystallineCoverRing P
  let α : A →+* B := (crystallineCoverMap P).toRingHom
  have hp : IsSMulRegular B (p : B) := by
    change Function.Injective (fun x : B => (p : B) * x)
    exact crystallineCover_p_regular P
  apply completeTorAmplitude_two_of_modP p α P.generator hp 2
  have hβ : (Ideal.Quotient.mk (Ideal.span {(p : B)})).comp α = coverMapToModP P := by
    apply RingHom.ext
    intro a
    rfl
  intro L K q hq hL m hK i hi
  letI := hq
  have hb := coverMapToModP_homology_isZero_below P hF hR q
    (semifreeComplex_isKFlat hL) m hK i hi
  change IsZero ((baseChange ((Ideal.Quotient.mk (Ideal.span {(p : B)})).comp α) L).homology i)
  rw [hβ]
  exact hb

/-- 概要：結晶被覆の完全 Tor 振幅は有限。
方針：実際の模型の上界三を有限性の証人にする。
規約：BS 著者版 Construction 6.1。
使われ方：Lemma 4.22 の有限振幅の入力。 -/
theorem crystallineCoverMap_finiteTorAmplitude
    (hF : IsCompletelyFlat (Ideal.span {coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    ∃ c : ℕ, HasCochainCompleteTorAmplitude
      (crystallineCoverMap P).toRingHom ![(p : A), P.generator] c :=
  ⟨3, crystallineCoverMap_torAmplitude P hF hR⟩

/-- 概要：普遍 prism の結晶被覆は完全 Tor 上界三を持つ。
方針：普遍向き付き prism の d 完全平坦性と A/d の p 正則性を直接入力する。
規約：BS 著者版 Example 3.4、Construction 6.1、Construction 6.1。
使われ方：普遍的な帰着の古典的な有限振幅。 -/
theorem universal_crystallineCoverMap_torAmplitude :
    HasCochainCompleteTorAmplitude
      (crystallineCoverMap (universalOrientedPrism.{u} p)).toRingHom
      ![(p : UniversalOrientedPrismRing.{u} p), (universalOrientedPrism.{u} p).generator] 3 :=
  crystallineCoverMap_torAmplitude (universalOrientedPrism.{u} p)
    (universalOrientedPrism_frobenius_isCompletelyFlat p)
    (universalOrientedPrism_mod_generator_p_regular p)

end SerrePositivity.BhattScholze.Prismatic.Construction61

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Construction 6.1" (partial := component) "BS-W17 H1・H2（11-11）：被覆 B と α、式 (6)、(1) 保存性と (2) 有限 Tor 振幅（上界 3）を上に有界でない複体で本体に。D77：原典の「Frobenius が平坦」の代わりに d 完全平坦性を入力（普遍の場合は K2）。(3) Lemma 4.20 は G10 の後"] _root_.SerrePositivity.BhattScholze.Prismatic.Construction61.crystallineCoverMap_torAmplitude
