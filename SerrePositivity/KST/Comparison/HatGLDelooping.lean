module

public import SerrePositivity.KST.Comparison.GrouplikeComparison
public import SerrePositivity.KST.Comparison.GrouplikeGL
public import SerrePositivity.KST.Comparison.DGAlgebra

/-!
# ĜL の群状モノイドの delooping への特殊化

概要：π₀ で可逆な行列のモノイドの標準群完備化写像は局所化同型である。
方針：実際の成分の群性を、群状モノイドの Segal 比較へ渡す。
規約：KST 式 (2.2) と Lemma 2.13 の有限 rank の比較。安定 rank と π_n の計算は別途接続する。
使われ方：ΓA の行列の bar の分類空間と loop の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory
open SerrePositivity.SimplicialModel

/--
概要：単体的環の ĜL_r の標準群完備化写像は局所化同型である。
方針：π₀ĜL_r と GL_r(π₀A) の同型から証明した群状性を使う。
規約：各単体次数の行列の可逆性は要求しない。
使われ方：KST Lemma 2.13 の有限 rank の delooping。
-/
theorem hatGLGroupCompletionMap_localized_isIso (A : SimplicialObject RingCat.{u}) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidGroupCompletionMap (hatGLMonoidObject A r))) :=
  monoidGroupCompletionMap_localized_isIso _ (hatGL_isGrouplike A r)

/--
概要：dg 代数の ΓA の ĜL_r の標準群完備化写像は局所化同型である。
方針：単体的環についての比較を実際の ΓA に適用する。
規約：cochain 規約の connective な入力の Γ は既存の truncation によるもの。
使われ方：dg 代数の分類空間の比較の入口。
-/
theorem dgAlgebraHatGLGroupCompletionMap_localized_isIso
    (R : Type u) [CommRing R] (A : DGAlgebraModel R) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map (monoidGroupCompletionMap (dgAlgebraHatGL R A r))) :=
  hatGLGroupCompletionMap_localized_isIso (dgAlgebraGamma R A) r

end SerrePositivity.KST.Comparison
