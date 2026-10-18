module

public import SerrePositivity.KST.DerivedBlowup.Charts
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Tactic.Abel

/-!
概要：KST Def3.1 の重なりにおける Koszul 生成元の変換を線形写像として構成する。
方針：省略された pivot 生成元を0として扱い、e_j^(k) を e_j^(i)−(S_j/S_k)e_k^(i) へ送る。
規約：この段階は Koszul の次数−1の生成加群。外積と微分への延長は別途証明する。
使われ方：チャートの cdga の貼り合わせを実際の可逆基底変換から構成する。
-/

@[expose] public noncomputable section

universe v w

namespace SerrePositivity.KST.DerivedBlowup

variable {I : Type v} [DecidableEq I] {B : Type w} [CommRing B]

/-- 概要：Koszul 生成加群で pivot 生成元を0とした標準ベクトル。
方針：pivot 以外を Finsupp の標準基底にする。規約：KST Def3.1 の r本の関係式。
使われ方：pivot を含む添字で基底変換を一様に表す。 -/
def koszulGenerator (i j : I) : ChartIndex i →₀ B :=
  if h : j = i then 0 else Finsupp.single ⟨j, h⟩ 1

@[simp] theorem koszulGenerator_self (i : I) : koszulGenerator (B := B) i i = 0 := by
  simp [koszulGenerator]

@[simp] theorem koszulGenerator_other (i : I) (j : ChartIndex i) :
    koszulGenerator (B := B) i j.val = Finsupp.single j 1 := by
  simp [koszulGenerator, j.property]

/-- 概要：チャート間の Koszul 生成元の線形変換。
方針：関係式の変換に対応する列ベクトルを linearCombination で延長する。
規約：KST §3.1 の重なり、s=S_k^(i)。使われ方：外積に延長する基底変換の元データ。 -/
def koszulGeneratorMap (i k : I) (x : I → B) (s : Bˣ) :
    (ChartIndex k →₀ B) →ₗ[B] (ChartIndex i →₀ B) :=
  Finsupp.linearCombination B (fun j : ChartIndex k =>
    koszulGenerator i j.val - normalizeCoordinates x s j.val • koszulGenerator i k)

/-- 概要：線形変換は pivot を含む全生成元に同じ公式を持つ。
方針：省略された pivot では単元律、それ以外では自由加群の普遍性。
規約：KST Def3.1、s の値は k 座標。使われ方：cocycle と逆基底変換の計算。 -/
theorem koszulGeneratorMap_generator (i k j : I) (x : I → B) (s : Bˣ)
    (hs : ↑s = x k) :
    koszulGeneratorMap i k x s (koszulGenerator k j) =
      koszulGenerator i j - normalizeCoordinates x s j • koszulGenerator i k := by
  by_cases h : j = k
  · subst j
    rw [koszulGenerator_self, map_zero, normalizeCoordinates_pivot x k s hs,
      one_smul, sub_self]
  · simp [koszulGenerator, h, koszulGeneratorMap]

/-- 概要：三重重なりで Koszul 生成元の変換は厳密な cocycle を満たす。
方針：二回の変換に現れる中間の基底ベクトルの係数が相殺する。
規約：KST §3.1、s=S_k^(i)、t=S_l^(k)。使われ方：cdga の貼り合わせの次数−1の整合性。 -/
theorem koszulGeneratorMap_cocycle_generator (i k l j : I) (x : I → B) (s t : Bˣ)
    (hs : ↑s = x k) (ht : ↑t = normalizeCoordinates x s l) :
    koszulGeneratorMap i k x s
        (koszulGeneratorMap k l (normalizeCoordinates x s) t (koszulGenerator l j)) =
      koszulGeneratorMap i l x (s * t) (koszulGenerator l j) := by
  have hst := transitionUnit_cocycle x l s t ht
  rw [koszulGeneratorMap_generator k l j _ t ht, map_sub, map_smul,
    koszulGeneratorMap_generator i k j x s hs,
    koszulGeneratorMap_generator i k l x s hs,
    koszulGeneratorMap_generator i l j x (s * t) hst, ← ht, smul_sub, smul_smul]
  have hc : normalizeCoordinates (normalizeCoordinates x s) t j * ↑t =
      normalizeCoordinates x s j := by
    unfold normalizeCoordinates
    rw [mul_assoc, t.inv_mul, mul_one]
  rw [hc, ← congrFun (normalizeCoordinates_cocycle x s t) j]
  abel

/-- 概要：Koszul 基底変換の線形写像そのものの cocycle。
方針：自由加群の生成元についての cocycle を線形に延長する。
規約：KST Def3.1 の三重重なり。使われ方：外積の関手性に渡す射の等式。 -/
theorem koszulGeneratorMap_cocycle (i k l : I) (x : I → B) (s t : Bˣ)
    (hs : ↑s = x k) (ht : ↑t = normalizeCoordinates x s l) :
    (koszulGeneratorMap i k x s).comp
        (koszulGeneratorMap k l (normalizeCoordinates x s) t) =
      koszulGeneratorMap i l x (s * t) := by
  apply Finsupp.lhom_ext
  intro j c
  have hsingle : Finsupp.single j c = c • koszulGenerator l j.val := by simp
  change koszulGeneratorMap i k x s
      (koszulGeneratorMap k l (normalizeCoordinates x s) t (Finsupp.single j c)) = _
  rw [hsingle, map_smul, map_smul, map_smul]
  exact congrArg (fun z => c • z) (koszulGeneratorMap_cocycle_generator i k l j.val x s t hs ht)

/-- 概要：同じ pivot での Koszul 基底変換は恒等。
方針：省略された pivot ベクトルが0であることを使う。
規約：KST §3.1 の恒等遷移。使われ方：基底変換の逆写像。 -/
@[simp] theorem koszulGeneratorMap_self (i : I) (x : I → B) :
    koszulGeneratorMap i i x 1 = LinearMap.id := by
  apply Finsupp.lhom_ext
  intro j c
  simp [koszulGeneratorMap]

omit [DecidableEq I] in
/-- 概要：逆単元での規格化は元の座標を回収する。
方針：座標 cocycle と単元逆元律を使う。規約：KST Def3.1 の往復遷移。
使われ方：Koszul 基底変換の反対側の係数を同定する。 -/
@[simp] theorem normalizeCoordinates_inverse (x : I → B) (s : Bˣ) :
    normalizeCoordinates (normalizeCoordinates x s) s⁻¹ = x := by
  rw [normalizeCoordinates_cocycle, mul_inv_cancel]
  funext j
  simp [normalizeCoordinates]

/-- 概要：Koszul 生成元の変換は逆単元による変換と相殺する。
方針：三重 cocycle を i→k→i に特殊化する。
規約：KST Def3.1、元の pivot 座標は1。使われ方：可逆基底変換の構成。 -/
theorem koszulGeneratorMap_inverse (i k : I) (x : I → B) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) :
    (koszulGeneratorMap i k x s).comp
        (koszulGeneratorMap k i (normalizeCoordinates x s) s⁻¹) = LinearMap.id := by
  have ht : ↑s⁻¹ = normalizeCoordinates x s i := by
    rw [normalizeCoordinates, hi, one_mul]
  simpa only [mul_inv_cancel, koszulGeneratorMap_self] using
    koszulGeneratorMap_cocycle i k i x s s⁻¹ hs ht

/-- 概要：チャートの Koszul 生成加群間の実際の可逆基底変換。
方針：cocycle と規格化の逆変換から両側逆を構成する。
規約：KST §3.1、外積に延長する前の線形同型。使われ方：導来チャートの cdga 同型。 -/
def koszulGeneratorEquiv (i k : I) (x : I → B) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) :
    (ChartIndex k →₀ B) ≃ₗ[B] (ChartIndex i →₀ B) :=
  LinearEquiv.ofLinearMap (koszulGeneratorMap i k x s)
    (koszulGeneratorMap k i (normalizeCoordinates x s) s⁻¹)
    (koszulGeneratorMap_inverse i k x s hi hs) (by
      have ht : ↑s⁻¹ = normalizeCoordinates x s i := by
        rw [normalizeCoordinates, hi, one_mul]
      have h := koszulGeneratorMap_inverse k i (normalizeCoordinates x s) s⁻¹
        (normalizeCoordinates_pivot x k s hs) ht
      simpa only [normalizeCoordinates_inverse, inv_inv] using h)

end SerrePositivity.KST.DerivedBlowup
