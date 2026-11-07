-- 将来の置き場所：共有層（HomologicalAlgebra/Cosimplicial/Bockstein など。調整役と相談）。BS 固有ではない。
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md G-A1-2。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.HomologicalAlgebra.Cosimplicial.Bockstein
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

/-! ## 正則元による短完全列 0 → C/d → C/d² → C/d → 0 -/

variable (C : CosimplicialObject CommRingCat.{u}) (d : ∀ n : SimplexCategory, C.obj n)
  (hd_nat : ∀ {m n} (θ : m ⟶ n), C.map θ (d m) = d n)
  (hd_reg : ∀ n, Function.Injective (fun x : C.obj n => d n * x))

/-- 概要：Bockstein は H^*(C/d) の cup 積に関する微分：β(a ∪ b) = β(a) ∪ b + (−1)^{|a|} a ∪ β(b)、β² = 0。
方針：d が各項で正則な複体 C への持ち上げで計算する（W9-I-21）：a ∈ C^i/d の余輪体の持ち上げ ã について ∂ã = d·b と書くと d·∂b = ∂²ã = 0、
正則性で ∂b = 0、よって β²[a] = 0（β の二回の合成は同じ短完全列の長完全列の隣接二射ではないので「合成が零」では出ない）。
Leibniz は ∂(ã ∪ c̃) = ∂ã ∪ c̃ + (−1)^i ã ∪ ∂c̃ を d で割る（`cochainDifferential_cup`）。
規約：cup 積は `CosimplicialCupProduct`。
使われ方：H^*(Ō) が dg 環であること（Constr 4.9）。 -/
theorem bockstein_leibniz (k : Type u) [CommRing k]
    (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C) (i j : ℕ)
    (a : cohomology (quotPow C d hd_nat 1) i) (b : cohomology (quotPow C d hd_nat 1) j) :
    let X := quotPow C d hd_nat 1
    let β := cupBockstein C d hd_nat hd_reg k ι
    β (i+j) (cohomologyCup X a b) =
      cast (congrArg (cohomology X) (show (i+1)+j = (i+j)+1 by omega)) (cohomologyCup X (β i a) b) +
      (-1 : ℤ)^i • cohomologyCup X a (β j b) := by
  sorry -- 共鎖の Leibniz 則を正則元で割ってコホモロジーに降ろす

theorem bockstein_sq (k : Type u) [CommRing k] (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C) (i : ℕ) :
    regularBockstein C d hd_nat hd_reg k ι i ≫ regularBockstein C d hd_nat hd_reg k ι (i + 1) = 0 := by
  sorry -- 正則な持ち上げの計算（W9-I-21）

/-- 概要：Bockstein は余単体的環の射で自然（d を d に写す射について）。
方針：連結準同型の自然性。
規約：—
使われ方：Lemma 4.10 の「関手性で一般へ」、模型の取り替え。 -/
theorem bockstein_natural (k : Type u) [CommRing k]
    (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C)
    (C' : CosimplicialObject CommRingCat.{u}) (d' : ∀ n, C'.obj n)
    (hd' : ∀ {m n} (θ : m ⟶ n), C'.map θ (d' m) = d' n)
    (hr' : ∀ n, Function.Injective (fun x : C'.obj n => d' n * x))
    (g : C ⟶ C') (hg : ∀ n, g.app n (d n) = d' n) (i : ℕ) (a : cohomology (quotPow C d hd_nat 1) i) :
    let X := quotPow C d hd_nat 1
    let Y := quotPow C' d' hd' 1
    let q := quotPowMap C d hd_nat d' hd' g hg 1
    cohomologyMap X Y q (i+1) (cupBockstein C d hd_nat hd_reg k ι i a) =
      cupBockstein C' d' hd' hr' k (ι ≫ g) i (cohomologyMap X Y q i a) := by
  sorry -- g が誘導する k 加群の短完全列の射に連結準同型の自然性を適用

end SerrePositivity.Cosimplicial
