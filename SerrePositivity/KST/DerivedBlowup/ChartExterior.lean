module

public import SerrePositivity.KST.DerivedBlowup.KoszulDifferential
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
概要：KST Def3.1 のチャートの Koszul 外積代数と収縮微分を構成する。
方針：既存 ExteriorAlgebra と CliffordAlgebra の contraction を使う。
規約：ここでは総外積代数と平方零の作用素を構成し、整数次数の dg 圏への装備は別段階。
使われ方：Koszul 生成元の基底変換を全外積へ延長し、微分との可換性を検証する。
-/

@[expose] public noncomputable section

universe v w

namespace SerrePositivity.KST.DerivedBlowup

variable {I : Type v} [DecidableEq I] {B : Type w} [CommRing B]

/-- 概要：チャート Koszul の総外積代数。方針：次数−1の生成加群の外積を取る。
規約：KST Def3.1、係数環は重なり環でもよい。使われ方：Koszul cdga の積の模型。 -/
abbrev ChartExterior (i : I) := ExteriorAlgebra B (ChartIndex i →₀ B)

/-- 概要：Koszul 関係式による外積代数の収縮微分。
方針：生成元上の微分に既存の contractLeft を適用する。
規約：KST Def3.1、平方零に正則性は不要。使われ方：貼り合わせの微分条件。 -/
def chartExteriorDifferential (a x : I → B) (i : I) : ChartExterior (B := B) i →ₗ[B]
    ChartExterior (B := B) i :=
  CliffordAlgebra.contractLeft (Q := 0) (chartKoszulDifferential a x i)

omit [DecidableEq I] in
/-- 概要：外積代数の収縮微分は平方零。方針：contractLeft の平方零定理を用いる。
規約：KST Def3.1 の Koszul 微分。使われ方：整数次数の複体に装備する微分律。 -/
theorem chartExteriorDifferential_sq (a x : I → B) (i : I) (z : ChartExterior (B := B) i) :
    chartExteriorDifferential a x i (chartExteriorDifferential a x i z) = 0 :=
  CliffordAlgebra.contractLeft_contractLeft _ z

/-- 概要：Koszul 基底変換を外積代数全体に延長する。
方針：ExteriorAlgebra.map を使い、乗法を保存する実際の代数射を作る。
規約：KST §3.1、重なりの同一係数環上の写像。使われ方：チャート cdga の遷移。 -/
def chartExteriorMap (i k : I) (x : I → B) (s : Bˣ) :
    ChartExterior (B := B) k →ₐ[B] ChartExterior (B := B) i :=
  ExteriorAlgebra.map (koszulGeneratorMap i k x s)

/-- 概要：外積代数の遷移は全次数で厳密な cocycle を満たす。
方針：生成元写像の cocycle と外積の関手性を合わせる。
規約：KST Def3.1 の三重重なり。使われ方：全 Koszul 代数の貼り合わせ。 -/
theorem chartExteriorMap_cocycle (i k l : I) (x : I → B) (s t : Bˣ)
    (hs : ↑s = x k) (ht : ↑t = normalizeCoordinates x s l) :
    (chartExteriorMap i k x s).comp (chartExteriorMap k l (normalizeCoordinates x s) t) =
      chartExteriorMap i l x (s * t) := by
  rw [chartExteriorMap, chartExteriorMap, ExteriorAlgebra.map_comp_map,
    koszulGeneratorMap_cocycle i k l x s t hs ht]
  rfl

/-- 概要：外積代数の遷移は Koszul の収縮微分を保つ。
方針：係数・和・生成元の左乗法による帰納法で次数−1の可換性を延長する。
規約：KST §3.1、x_i=1、s=x_k。使われ方：チャート cdga の遷移の微分適合性。 -/
theorem chartExteriorMap_differential (a x : I → B) (i k : I) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) (z : ChartExterior (B := B) k) :
    chartExteriorDifferential a x i (chartExteriorMap i k x s z) =
      chartExteriorMap i k x s (chartExteriorDifferential a (normalizeCoordinates x s) k z) := by
  change CliffordAlgebra.contractLeft (Q := 0) (chartKoszulDifferential a x i)
      (ExteriorAlgebra.map (koszulGeneratorMap i k x s) z) =
    ExteriorAlgebra.map (koszulGeneratorMap i k x s)
      (CliffordAlgebra.contractLeft (Q := 0)
        (chartKoszulDifferential a (normalizeCoordinates x s) k) z)
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | ι_mul z m hz =>
    rw [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      CliffordAlgebra.contractLeft_ι_mul, map_sub, map_smul, map_mul,
      ExteriorAlgebra.map_apply_ι]
    rw [hz]
    have hm := LinearMap.congr_fun (koszulGeneratorMap_differential a x i k s hi hs) m
    exact congrArg (fun c => c • ExteriorAlgebra.map (koszulGeneratorMap i k x s) z -
      ExteriorAlgebra.ι B (koszulGeneratorMap i k x s m) *
        ExteriorAlgebra.map (koszulGeneratorMap i k x s)
          (CliffordAlgebra.contractLeft (Q := 0)
            (chartKoszulDifferential a (normalizeCoordinates x s) k) z)) hm

/-- 概要：チャートの Koszul 外積代数の可逆な基底変換。
方針：生成加群の両側逆を外積の関手性で持ち上げる。
規約：KST Def3.1、微分との整合は chartExteriorMap_differential。
使われ方：重なりにおける次数付き dg 代数同型の基礎となる代数同型。 -/
def chartExteriorEquiv (i k : I) (x : I → B) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) :
    ChartExterior (B := B) k ≃ₐ[B] ChartExterior (B := B) i :=
  AlgEquiv.ofAlgHom (chartExteriorMap i k x s)
    (chartExteriorMap k i (normalizeCoordinates x s) s⁻¹)
    (by
      rw [chartExteriorMap, chartExteriorMap, ExteriorAlgebra.map_comp_map,
        koszulGeneratorMap_inverse i k x s hi hs, ExteriorAlgebra.map_id])
    (by
      have ht : ↑s⁻¹ = normalizeCoordinates x s i := by
        rw [normalizeCoordinates, hi, one_mul]
      have h := koszulGeneratorMap_inverse k i (normalizeCoordinates x s) s⁻¹
        (normalizeCoordinates_pivot x k s hs) ht
      rw [normalizeCoordinates_inverse, inv_inv] at h
      rw [chartExteriorMap, chartExteriorMap, ExteriorAlgebra.map_comp_map, h,
        ExteriorAlgebra.map_id])

end SerrePositivity.KST.DerivedBlowup
