-- 将来の置き場所：EInfinity の上（余単体的可換環の Tot の E∞ 構造。BS 固有ではない。調整役と相談）
-- 設計書：formalization-plans/bhatt-scholze/a1-design.md G-A1-11、a2-design.md §2.2。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.Perfectoidization.Comparison
public import SerrePositivity.InfinityCategories.Derived.Homology
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
-- 本ファイルは drafts/Shared/CosimplicialCupProduct.lean と drafts/Sheaves/{CechConerveLimit,CAlgValued}.lean を使う。

/-!
# 余単体的可換環の Tot の E∞ 構造と、CAlg 値の脚注 10

## 概要
余単体的可換 A 代数 X^• の非正規化余鎖複体に Barratt–Eccles 作用素の作用を入れ（McClure–Smith、Berger–Fresse：余単体的可換環の
余鎖は E∞ 代数）、CAlg_A の対象 Tot_{E∞}(X^•) を得る。その下の複体は交代余面複体、H^* の環構造は Alexander–Whitney の cup 積
（Shared/CosimplicialCupProduct）に一致する。さらに、Tot_{E∞}(X^•) は CAlg_A における余単体的対象 [n] ↦ X^n の Δ 上の極限で、
弱終対象の Čech 脈体の補題（S3）の CAlg_A 版により、環の前層の CAlg 値 RΓ が Čech–Alexander 模型の Tot_{E∞} に E∞ 代数として一致する。

## 方針
E∞ 構造は EInfinity の Barratt–Eccles 作用素（`Operad`、`CochainComonoid` などの余鎖の余モノイド構造）で、余単体的可換環の
正規化余鎖に McClure–Smith の構成を当てる。極限との同一視は、U : CAlg_A → D(A) が極限錐を保ち反映すること（Sheaves/CAlgValued）と、
D(A) 側の G10（Δ 上の極限 ＝ 全複体）。

## 規約
E∞ 構造の明示的な構成は EInfinity の operad の形に合わせる（要確認：EInfinity の Barratt–Eccles 作用素が余鎖に作用する形で公開されているか）。
正規化と非正規化は擬同型（Dold–Kan）。ただし W9-I-24：複体の擬同型だけでは E∞ 構造の比較にならない。**正規化模型を選んで** CAlg の
ホモトピー整合的な錐を構成し（U で見た underlying cone が各項への射影の錐に一致すること）、AW 積との比較を示す。非正規化模型への
E∞ 構造の移送を使うなら、その比較射を明記する。

## 使われ方
A2-2（Δ_0 の CAlg 値が Čech–Alexander 模型の Tot_{E∞}）、A1 の D27（模型の cup 積と抽象的な環構造の一致）、A4（Frobenius 余極限の E∞ 構造）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.Cosimplicial

open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.F2.Presentable
open SerrePositivity.EInfinity.BarrattEccles SerrePositivity.EInfinity.Perfectoidization
attribute [local instance] HasDerivedCategory.standard

variable (A : Type u) [CommRing A]

/-- 概要：余単体的可換 A 代数（各項が A 代数で構造射が A 代数の射）。
方針：`CosimplicialObject (Under (CommRingCat.of A))` または `CosimplicialObject CommRingCat` ＋ A からの射。
規約：—
使われ方：Tot_{E∞} の入力。 -/
abbrev CosimplicialAlgebra := CosimplicialObject (Under (CommRingCat.of A))

/-- 概要：Tot_{E∞}(X^•)：非正規化（または正規化）余鎖複体に Barratt–Eccles の E∞ 構造を入れた CAlg_A の頂点。
方針：McClure–Smith の余単体的可換環の E∞ 構造（Berger–Fresse の Barratt–Eccles 作用素の余鎖への作用の余単体的版）。
規約：cofibrant 置換は CAlg_A（cofibrant 代数の局所化の nerve）の構成に含める。
使われ方：A2 の Δ_0。
基盤待ち：正規化余鎖への作用と E∞ 錐の両立。 -/
def totEInfinityFunctor : nerve (CosimplicialAlgebra A) ⟶ CAlg_R A := by
  sorry -- 正規化余鎖の Barratt–Eccles 構造を余単体的代数の射について関手化する

abbrev totEInfinity (X : CosimplicialAlgebra A) :=
  (totEInfinityFunctor A).app _ (nerveVertex X)

/-- 小さい Δ の nerve だけを持ち上げ、各項を離散 E∞ 代数に送る。 -/
def totDiagram (X : CosimplicialAlgebra A) :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶ CAlg_R A := by
  let D : (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶ nerve (Under (CommRingCat.of A)) :=
    { app := fun _ => ↾fun t => (X.mapComposableArrows _).obj t.down
      naturality := by sorry } -- X による射列の像は単体の制限と可換
  exact D ≫ algebraEmbedding A

/-- 概要：Tot_{E∞} の下の複体は交代余面複体（`alternatingCofaceMapComplex`）。
方針：構成から。
規約：D(A) の同値。
使われ方：A0 の D(A) 値の Tot との一致。 -/
def totEInfinity_forget (X : CosimplicialAlgebra A) (i : ℕ) :
    derivedInfinityHomology A (i : ℤ) ((cAlgForgetDerived A).app _ (totEInfinity A X)) ≅
      ((AlgebraicTopology.alternatingCofaceMapComplex _).obj (X ⋙ discreteAlgebraModule A)).homology i := by
  sorry -- 正規化と非正規化の比較。右辺は A 加群としてのコホモロジー

/-- A 線形な比較を、cup に使うコホモロジーの加法群に移す。 -/
def totEInfinity_forget_cohomology (X : CosimplicialAlgebra A) (i : ℕ) :
    derivedInfinityHomology A (i : ℤ) ((cAlgForgetDerived A).app _ (totEInfinity A X)) ≃+
      cohomology (X ⋙ Under.forget _) i := by
  refine (totEInfinity_forget A X i).toLinearEquiv.toAddEquiv.trans
    (AddEquiv.trans ?_ (cohomologyEquivHomology (X ⋙ Under.forget _) i).symm)
  sorry -- 加群から加法群への忘却は交代余面複体とホモロジーを保つ

/-- 交代余面複体は次数零から始まる。 -/
theorem totEInfinity_forget_negative (X : CosimplicialAlgebra A) (i : ℤ) (hi : i < 0) :
    Limits.IsZero (derivedInfinityHomology A i ((cAlgForgetDerived A).app _ (totEInfinity A X))) := by
  sorry -- 正規化余鎖を整数次数へ零延長した模型には負次数のコホモロジーがない

/-- 概要：Tot_{E∞} の H^* の環構造は cup 積（Shared/CosimplicialCupProduct）に一致。
方針：E∞ 構造の二項演算 μ_0 が Alexander–Whitney の cup 積（Barratt–Eccles の次数 0 の成分）。
規約：—
使われ方：A1 の D27。×：全次数の π_* の積を与える基盤名がなく、π₀ の環だけではこの比較を述べられない（M14）。 -/
theorem totEInfinity_cohomologyRing (X : CosimplicialAlgebra A) : True := by trivial

/-- 概要：Tot_{E∞}(X^•) は CAlg_A における余単体的図式 [n] ↦ X^n（離散 E∞ 代数）の Δ 上の極限。
方針：まず CAlg_A のホモトピー整合的な錐（正規化模型から）を構成し、その underlying cone を各項への射影の錐と同一視してから、U が極限錐を
保ち反映すること（Sheaves/CAlgValued）と D(A) 側の G10（Δ 上の極限 ＝ 全複体）を使う（W9-I-24：「各項への射影」だけでは CAlg の錐を指定していない）。
規約：錐は CAlg_A の JoinCone。
使われ方：CAlg 値の脚注 10。 -/
def totEInfinityCone (X : CosimplicialAlgebra A) :
    {c : JoinCone (totDiagram A X) // c.vertex = totEInfinity A X} := by
  sorry -- 正規化 E∞ 模型から離散な各項への射影を整合的な錐にする（W9-I-24）

theorem totEInfinity_isLimitCone (X : CosimplicialAlgebra A) :
    IsLimitCone (totEInfinityCone A X).val := by
  sorry -- 忘却後は G10 の Δ 極限錐。U の極限反映で戻す

/-- 概要：余単体的 A 代数の射 X → Y は Tot_{E∞} の E∞ 代数の射を誘導し、関手的。
方針：構成の自然性。
規約：—
使われ方：Δ_0 の多項式代数の射についての関手性、Frobenius（半線形は別）。 -/
def totEInfinity_map {X Y : CosimplicialAlgebra A} (f : X ⟶ Y) :
    SSet.Edge (totEInfinity A X) (totEInfinity A Y) :=
  (nerve.edgeMk f).map (totEInfinityFunctor A)

/-- 概要：脚注 10 の CAlg 版：弱終対象 U の Čech 脈体 U_• と環の前層 O について、CAlg_A 値の RΓ(O) ≃ Tot_{E∞}(O(U_•))（E∞ 代数として）。
方針：S3 を E = CAlg_A で（`isLimitCone_iff_restrict_cech`）と `totEInfinity_isLimitCone`。
規約：O は層（Cor 3.12 の CAlg 版、`isSheaf_iff_forget`）。
使われ方：A2 の Δ_0 の CAlg 値 ＝ Čech–Alexander 模型の Tot_{E∞}。 -/
def derivedGlobalSectionsCAlg_eq_totEInfinity {𝒟 : Type u} [SmallCategory 𝒟]
    (J : GrothendieckTopology 𝒟) (hJ : Sheafification J (CAlg_R A)) (hA : IsPresentable (CAlg_R A))
    (O : 𝒟ᵒᵖ ⥤ Under (CommRingCat.of A)) (hO : IsSheaf J (ringPresheafToCAlg A O))
    (U : 𝒟) (hU : IsWeaklyTerminal U) (d : CechNerveData U) :
    VertexIso (derivedGlobalSectionsCAlg J A hJ hA (ringPresheafToCAlg A O))
      (totEInfinity A (d.obj.rightOp ⋙ O)) := by
  sorry -- S2 の層の RΓ と S3 で d に制限した錐を totEInfinity_isLimitCone と比較

end SerrePositivity.Cosimplicial
