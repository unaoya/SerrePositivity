-- 将来の置き場所：共有層（HomologicalAlgebra/Cosimplicial/Bockstein など。調整役と相談）。BS 固有ではない。
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md G-A1-2。基準コミット 972bb7f53。ビルドしない。
module

public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologySequence
-- 本ファイルは drafts/Shared/CosimplicialCupProduct.lean を import する。

/-!
# 余単体的加群の短完全列の Bockstein と Leibniz 則

## 概要
余単体的 k 加群の項ごとの短完全列 0 → M′ → M → M″ → 0 から交代余面複体の短完全列を作り、その連結準同型
β : H^i(M″) → H^{i+1}(M′) を Bockstein と呼ぶ。余単体的可換環 C^• と各項で正則な元 d について、0 → C/d →d→ C/d² → C/d → 0 の
Bockstein β : H^i(C/d) → H^{i+1}(C/d) は H^*(C/d) の cup 積に関する微分（β² = 0、Leibniz）で、H^*(C/d) を dg 環にする。

## 方針
Mathlib の `HomologicalComplex.HomologySequence`（短完全列の長完全列）を交代余面複体に適用する。Leibniz 則は余輪体の持ち上げの cup 積の計算。

## 規約
交代余面複体は非正規化。符号は連結準同型の Mathlib の規約に従う（A1 の紙の検証 3 で Cartier との一致のために固定する）。

## 使われ方
Constr 4.9（原典の β_I。向き付きなので捻りなし）、Lemma 4.10（β(f)² = 0）、η^1(df) := β(η^0 f)。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SerrePositivity.Cosimplicial

variable {k : Type u} [CommRing k]

/-- 概要：余単体的 k 加群の項ごとの短完全列。
方針：`CosimplicialObject (ModuleCat k)` の射二本と各項での完全性。
規約：項ごとの完全性を `ShortComplex.ShortExact` で。
使われ方：Bockstein の入力。 -/
structure CosimplicialShortExact (M' M M'' : CosimplicialObject (ModuleCat.{u} k)) where
  ι : M' ⟶ M
  π : M ⟶ M''
  /-- π ∘ ι = 0 をデータとして保持（W9-I-21）。係数は共通の基底 k（A または ℤ）に固定し、C⁰ を係数環にしない。 -/
  zero : ι ≫ π = 0
  exact : ∀ n : SimplexCategory, (ShortComplex.mk (ι.app n) (π.app n) (by sorry)).ShortExact

/-- 概要：交代余面複体の短完全列（項ごとの短完全列から）。
方針：`alternatingCofaceMapComplex` は加法的関手なので短完全列を保つ。
規約：—
使われ方：長完全列。 -/
def CosimplicialShortExact.cochainShortExact {M' M M''} (s : CosimplicialShortExact M' M M'') :
    (ShortComplex.mk (CosimplicialObject.alternatingCofaceMapComplex.map s.ι)
      (CosimplicialObject.alternatingCofaceMapComplex.map s.π) (by sorry)).ShortExact := by
  sorry

/-- 概要：Bockstein（連結準同型）β : H^i(M″) → H^{i+1}(M′)。
方針：`HomologicalComplex.HomologySequence.δ` または `ShortComplex.ShortExact.δ`。
規約：Mathlib の連結準同型の符号。
使われ方：Constr 4.9。 -/
def CosimplicialShortExact.bockstein {M' M M''} (s : CosimplicialShortExact M' M M'') (i : ℕ) :
    (CosimplicialObject.alternatingCofaceMapComplex.obj M'').homology i ⟶
      (CosimplicialObject.alternatingCofaceMapComplex.obj M').homology (i + 1) :=
  sorry -- s.cochainShortExact.δ i (i+1) rfl

/-! ## 正則元による短完全列 0 → C/d → C/d² → C/d → 0 -/

variable (C : CosimplicialObject CommRingCat.{u}) (d : ∀ n : SimplexCategory, C.obj n)
  (hd_nat : ∀ {m n} (θ : m ⟶ n), C.map θ (d m) = d n)
  (hd_reg : ∀ n, Function.Injective (fun x : C.obj n => d n * x))

/-- 概要：余単体的環 C の、各項で正則な（面写像で保たれる）元 d による商 C/d^k を余単体的環として。
方針：`Ideal.Quotient` と面写像の降下。
規約：d は基底から来る元（prism の生成元の像）を想定するが、ここでは一般。
使われ方：Ō_Δ の模型 C^•/dC^• と C^•/d²。 -/
def quotPow (k' : ℕ) : CosimplicialObject CommRingCat.{u} :=
  sorry -- n ↦ C.obj n ⧸ (d n)^k'

/-- 概要：短完全列 0 → C/d →d→ C/d² → C/d → 0（d 正則）。
方針：d 倍は C/d → C/d² へ単射（正則性）、像は dC/d²C、余核は C/d。
規約：加群として。係数は共通の基底環 k（prism の A、または ℤ）に固定する（C⁰ は一般には共通の係数環ではない、W9-I-21）。
使われ方：Bockstein β : H^i(C/d) → H^{i+1}(C/d)。 -/
def regularShortExact : True := trivial -- 要確認：係数環を固定して CosimplicialShortExact の形に

/-- 概要：Bockstein は H^*(C/d) の cup 積に関する微分：β(a ∪ b) = β(a) ∪ b + (−1)^{|a|} a ∪ β(b)、β² = 0。
方針：d が各項で正則な複体 C への持ち上げで計算する（W9-I-21）：a ∈ C^i/d の余輪体の持ち上げ ã について ∂ã = d·b と書くと d·∂b = ∂²ã = 0、
正則性で ∂b = 0、よって β²[a] = 0（β の二回の合成は同じ短完全列の長完全列の隣接二射ではないので「合成が零」では出ない）。
Leibniz は ∂(ã ∪ c̃) = ∂ã ∪ c̃ + (−1)^i ã ∪ ∂c̃ を d で割る（`cochainDifferential_cup`）。
規約：cup 積は `CosimplicialCupProduct`。
使われ方：H^*(Ō) が dg 環であること（Constr 4.9）。 -/
theorem bockstein_leibniz : True := by trivial

theorem bockstein_sq : True := by trivial

/-- 概要：Bockstein は余単体的環の射で自然（d を d に写す射について）。
方針：連結準同型の自然性。
規約：—
使われ方：Lemma 4.10 の「関手性で一般へ」、模型の取り替え。 -/
theorem bockstein_natural : True := by trivial

end SerrePositivity.Cosimplicial
