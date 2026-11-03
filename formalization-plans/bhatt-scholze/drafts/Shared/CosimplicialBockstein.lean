-- 将来の置き場所：共有層（HomologicalAlgebra/Cosimplicial/Bockstein など。調整役と相談）。BS 固有ではない。
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md G-A1-2。基準コミット 972bb7f53。ビルドしない。
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
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
def CosimplicialShortExact.cochainShortExact {M' M M''} (s : CosimplicialShortExact (k := k) M' M M'') :
    (ShortComplex.mk ((AlgebraicTopology.alternatingCofaceMapComplex _).map s.ι)
      ((AlgebraicTopology.alternatingCofaceMapComplex _).map s.π) (by sorry)).ShortExact := by
  sorry

/-- 概要：Bockstein（連結準同型）β : H^i(M″) → H^{i+1}(M′)。
方針：`HomologicalComplex.HomologySequence.δ` または `ShortComplex.ShortExact.δ`。
規約：Mathlib の連結準同型の符号。
使われ方：Constr 4.9。 -/
def CosimplicialShortExact.bockstein {M' M M''} (s : CosimplicialShortExact (k := k) M' M M'') (i : ℕ) :
    ((AlgebraicTopology.alternatingCofaceMapComplex _).obj M'').homology i ⟶
      ((AlgebraicTopology.alternatingCofaceMapComplex _).obj M').homology (i + 1) :=
  sorry -- s.cochainShortExact.δ i (i+1) rfl

/-! ## 正則元による短完全列 0 → C/d → C/d² → C/d → 0 -/

variable (C : CosimplicialObject CommRingCat.{u}) (d : ∀ n : SimplexCategory, C.obj n)
  (hd_nat : ∀ {m n} (θ : m ⟶ n), C.map θ (d m) = d n)
  (hd_reg : ∀ n, Function.Injective (fun x : C.obj n => d n * x))

/-- 概要：余単体的環 C の、各項で正則な（面写像で保たれる）元 d による商 C/d^k を余単体的環として。
方針：`Ideal.Quotient` と面写像の降下。
規約：d は基底から来る元（prism の生成元の像）を想定するが、ここでは一般。
使われ方：Ō_Δ の模型 C^•/dC^• と C^•/d²。 -/
def quotPow (C : CosimplicialObject CommRingCat.{u}) (d : ∀ n : SimplexCategory, C.obj n)
    (hd_nat : ∀ {m n} (θ : m ⟶ n), C.map θ (d m) = d n) (k' : ℕ) : CosimplicialObject CommRingCat.{u} where
  obj n := CommRingCat.of (C.obj n ⧸ Ideal.span {d n ^ k'})
  map {m n} θ := CommRingCat.ofHom (Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (C.map θ).hom)
    (by sorry)) -- hd_nat により (d m)^k' は標的の商で零
  map_id := by sorry -- 商の生成元上で恒等
  map_comp := by sorry -- 商の生成元上で C.map_comp

def quotProjection (j : ℕ) : C ⟶ quotPow C d hd_nat j where
  app n := CommRingCat.ofHom (Ideal.Quotient.mk _)
  naturality := by sorry -- 商の誘導射は商射と可換

def quotPowMap {C' : CosimplicialObject CommRingCat.{u}} (d' : ∀ n, C'.obj n)
    (hd' : ∀ {m n} (θ : m ⟶ n), C'.map θ (d' m) = d' n) (g : C ⟶ C')
    (hg : ∀ n, g.app n (d n) = d' n) (j : ℕ) :
    quotPow C d hd_nat j ⟶ quotPow C' d' hd' j where
  app n := CommRingCat.ofHom (Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (g.app n).hom)
    (by sorry)) -- hg により生成元の j 乗は商で零
  naturality := by sorry -- g の自然性を商へ降ろす

/-- 概要：係数環 k を固定した余単体的 k 加群としての読み替え（W9-I-21：係数は共通の基底 k、C⁰ ではない）。
方針：定数図式 k → C の射 ι に沿って各項を k 加群に。
規約：`CosimplicialObject (ModuleCat k)`。
使われ方：`regularShortExact`。 -/
def toModules (k : Type u) [CommRing k] (C : CosimplicialObject CommRingCat.{u})
    (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C) : CosimplicialObject (ModuleCat.{u} k) := sorry

include hd_reg in -- 11-03（D4-06）：body が sorry でも hd_reg を引数に残す（A1 の `htSequence` が渡す。def の body 依存の自動包含には頼らない）
/-- 概要：短完全列 0 → C/d →d→ C/d² → C/d → 0（d 正則）。
方針：d 倍は C/d → C/d² へ単射（正則性）、像は dC/d²C、余核は C/d。
規約：加群として。係数は共通の基底環 k（prism の A、または ℤ）に固定する（C⁰ は一般には共通の係数環ではない、W9-I-21）。
使われ方：Bockstein β : H^i(C/d) → H^{i+1}(C/d)。 -/
def regularShortExact (k : Type u) [CommRing k] (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C) :
    CosimplicialShortExact
      (toModules k (quotPow C d hd_nat 1) (ι ≫ quotProjection C d hd_nat 1))
      (toModules k (quotPow C d hd_nat 2) (ι ≫ quotProjection C d hd_nat 2))
      (toModules k (quotPow C d hd_nat 1) (ι ≫ quotProjection C d hd_nat 1)) :=
  sorry -- d 倍 C/d → C/d²（正則性で単射）、商 C/d² → C/d

/-- 概要：Bockstein β_i : H^i(C/d) → H^{i+1}(C/d)（上の短完全列の連結準同型）。 -/
def regularBockstein (k : Type u) [CommRing k] (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C) (i : ℕ) :=
  (regularShortExact C d hd_nat hd_reg k ι).bockstein i

/-- 共通の基底 k に関する加群コホモロジーを cup 側の加法群と比較する。 -/
def cohomologyEquivModuleHomology (k : Type u) [CommRing k] (X : CosimplicialObject CommRingCat.{u})
    (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ X) (i : ℕ) :
    cohomology X i ≃+ ((AlgebraicTopology.alternatingCofaceMapComplex _).obj (toModules k X ι)).homology i := by
  refine (cohomologyEquivHomology X i).trans ?_
  sorry -- 加群から加法群への忘却は交代和・ホモロジーを保つ

def cupBockstein (k : Type u) [CommRing k] (ι : (Functor.const SimplexCategory).obj (CommRingCat.of k) ⟶ C) (i : ℕ) :
    cohomology (quotPow C d hd_nat 1) i →+ cohomology (quotPow C d hd_nat 1) (i+1) :=
  let E := cohomologyEquivModuleHomology k (quotPow C d hd_nat 1) (ι ≫ quotProjection C d hd_nat 1)
  (E (i+1)).symm.toAddMonoidHom.comp
    ((regularBockstein C d hd_nat hd_reg k ι i).hom.toAddMonoidHom.comp (E i).toAddMonoidHom)

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
