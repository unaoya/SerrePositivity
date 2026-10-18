module

public import SerrePositivity.KST.Descent.RationalFixedPoints
public import SerrePositivity.KST.Descent.InvariantExactness

/-!
# (3.8) の置換表現と指定された対角比較

## 概要
G 集合上の積に逆元の添字置換で左表現を与え、既存の固定条件と一致させる。
推移的で非空なら、定数族への指定された対角写像が不変部分との同型になる。

## 方針
通常の不変部分に対する定数族の計算を Mathlib の表現と同変写像の API に接続する。

## 規約
これは (3.8) の π_* 側の置換作用の計算。hG の実構成との比較は含まない。
有限性や次数の有界性はこの代数計算には不要。

## 使われ方
論文 定理 3.1 の軌道正方形で、W のコピー上の作用が係数も含めて単なる置換である場合。
-/

@[expose] public section

open Representation

namespace SerrePositivity.KST.Descent

variable (G I M : Type*) [Group G] [MulAction G I] [AddCommGroup M] [Module ℚ M]

/-- 概要：積の添字の逆元による置換表現（論文 (3.8)）。
方針：`g` は族を `i ↦ v(g⁻¹ • i)` へ送る。
規約：係数 M 上の作用は自明で、添字だけを動かす。
使われ方：コピーの置換作用の通常の不変部分。 -/
def permutationRepresentation : Representation ℚ G (I → M) where
  toFun g := LinearMap.funLeft ℚ M (fun i ↦ g⁻¹ • i)
  map_one' := by
    ext v i
    change v ((1 : G)⁻¹ • i) = v i
    simp only [inv_one, one_smul]
  map_mul' g h := by
    ext v i
    change v ((g * h)⁻¹ • i) = v (h⁻¹ • (g⁻¹ • i))
    simp only [mul_inv_rev, mul_smul]

/-- 概要：置換表現の不変部分は既存の添字固定条件と一致（論文 (3.8)）。
方針：群元を逆元で取り直し、関数の等式を添字で評価する。
規約：既存の固定部分の値を変えずに比較する。
使われ方：定数族の計算を表現の API へ接続する。 -/
theorem permutationRepresentation_invariants_eq :
    (permutationRepresentation G I M).invariants = permutationInvariants G I M := by
  ext v
  change (∀ g : G, (fun i ↦ v (g⁻¹ • i)) = v) ↔ ∀ (g : G) (i : I), v (g • i) = v i
  constructor
  · intro hv g i
    simpa only [inv_inv] using congrFun (hv g⁻¹) i
  · intro hv g
    funext i
    exact hv g⁻¹ i

/-- 概要：推移的な置換表現の不変部分は一つのコピーの加群（論文 (3.8)）。
方針：指定した添字で評価し、逆に定数族を取る。
規約：添字 i₀ を明示し、安定化部分群の作用は自明である。
使われ方：有理 Shapiro の π_* 側の置換作用の計算。 -/
noncomputable def permutationRepresentationInvariantsEquiv [MulAction.IsPretransitive G I]
    (i₀ : I) : (permutationRepresentation G I M).invariants ≃ₗ[ℚ] M where
  toFun v := v.val i₀
  invFun x := ⟨fun _ ↦ x, fun _ ↦ rfl⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    have hv : v.val ∈ permutationInvariants G I M := by
      rw [← permutationRepresentation_invariants_eq]
      exact v.property
    exact permutationInvariants_constant G I M ⟨v.val, hv⟩ i₀ i
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 概要：元の加群から置換不変部分への指定された対角写像（論文 (3.8)）。
方針：元を定数族へ送る。
規約：添字の代表選択に依存しない写像そのものを定義する。
使われ方：幾何学的なコピーへの制限比較と同定する写像。 -/
noncomputable def permutationDiagonal : M →ₗ[ℚ] (permutationRepresentation G I M).invariants where
  toFun x := ⟨fun _ ↦ x, fun _ ↦ rfl⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 概要：推移的で非空な置換作用では指定された対角比較が同型（論文 (3.8)）。
方針：評価による線形同型の逆写像がこの対角写像であることを使う。
規約：無関係な抽象同型の存在ではなく、対角写像そのものの全単射性。
使われ方：軌道正方形の W とその閉中心上のコピーの比較。 -/
theorem permutationDiagonal_bijective [MulAction.IsPretransitive G I] [Nonempty I] :
    Function.Bijective (permutationDiagonal G I M) := by
  classical
  let i₀ : I := Classical.choice inferInstance
  exact (permutationRepresentationInvariantsEquiv G I M i₀).symm.bijective

variable {M} {N : Type*} [AddCommGroup N] [Module ℚ N]

/-- 概要：各コピーに同じ係数写像を作用させる同変写像（論文 (3.8) の自然性）。
方針：各添字で線形写像 φ を適用する。
規約：群は添字だけを置換し、φ はコピーに依存しない。
使われ方：制限・差・境界に対する置換不変部分の自然性。 -/
def permutationIntertwiningMap (φ : M →ₗ[ℚ] N) :
    IntertwiningMap (permutationRepresentation G I M) (permutationRepresentation G I N) where
  toLinearMap := LinearMap.pi fun i ↦ φ.comp (LinearMap.proj i)
  isIntertwining' _ := rfl

/-- 概要：対角比較は同じ係数写像のコピーへの適用と可換（論文 (3.8)）。
方針：両辺が φ x の定数族であることを確認する。
規約：不変性の証明項による差はない。
使われ方：指定比較が長完全列の写像と両立することの確認。 -/
theorem permutationDiagonal_naturality (φ : M →ₗ[ℚ] N) (x : M) :
    invariantMap (permutationIntertwiningMap G I φ) (permutationDiagonal G I M x) =
      permutationDiagonal G I N (φ x) := rfl

end SerrePositivity.KST.Descent
