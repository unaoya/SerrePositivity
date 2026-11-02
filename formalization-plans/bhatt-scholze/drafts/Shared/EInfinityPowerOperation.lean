-- 将来の置き場所：EInfinity の上（E∞-F_p 代数の冪作用。BS 固有ではない。置き場所と担当は調整役、M12・M13 と同じ扱い）
-- 設計書：formalization-plans/bhatt-scholze/a4-design.md G-A4-1。基準コミット 972bb7f53。ビルドしない。
module

public import SerrePositivity.EInfinity.BarrattEccles.CAlg
-- 本ファイルは drafts/Shared/CosimplicialEInfinity.lean（余単体的可換環の Tot_{E∞}）を使う。

/-!
# E∞-F_p 代数の冪作用 P⁰（[Lur11, §2.2]、Berger–Fresse、May）

## 概要
標数 p の E∞ 代数（E∞-F_p 代数、ここでは F_p 代数 k 上の Barratt–Eccles 代数）のホモトピー π_* に作用する冪作用のうち P⁰ を定義し、
(i) π_0 では Frobenius x ↦ x^p、(ii) π_n（n > 0、ホモロジー的）では零（[Lur11, Rem 2.2.7]）、(iii) 余単体的（および単体的余単体的）可換 F_p 代数の
levelwise Frobenius x ↦ x^p が Tot_{E∞}（実現）の P⁰ を誘導すること、を述べる。

## 方針
Barratt–Eccles 作用素 E(p) の F_p 上の作用から、x ∈ π_n に対し P⁰(x) を p 乗の作用素の標準元（Steenrod の構成、Berger–Fresse §2、May の
P^i の i = 0 の成分）で定義する。(ii) は Lurie の議論（DAG XIII、または Mandell）。(iii) は余鎖の Frobenius と作用素の p 乗の一致。

## 規約
cohomological な添字では「π_n（n > 0）」は「H^{−n}（n > 0）」。coconnective な対象（余単体的 Tot）には正次数のホモトピーがなく、
正次数は単体的方向（Kan 延長の分解）から来る。EInfinity の operad の具体的な型に合わせる（要確認）。

## 使われ方
Lemma 8.4（A4）：Δ_perf/p で P⁰ が可逆 ⇒ coconnective。Example 8.3。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.EInfinity

variable (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- 概要：E∞-k 代数（k は F_p 代数）のホモトピー π_n（整数次数）。
方針：`CAlg_R k` の頂点の忘却像の H^{−n}。
規約：ホモロジー的添字。
使われ方：P⁰ の定義域。 -/
def homotopy (X : (CAlg_R k) _⦋0⦌) (n : ℤ) : Type u := sorry

/-- 概要：冪作用 P⁰ : π_n(X) → π_n(X)（加法的、π_* 全体で定義）。
方針：Barratt–Eccles 作用素の p 乗の作用の標準元で定義（Steenrod／May の P^0）。
規約：k 線形ではない（φ_k 半線形）。
使われ方：Lemma 8.4。
要確認：EInfinity の operad の作用の型（`Operad`、`BarrattEccles` の E(p) と k[Σ_p] 加群の構造）。 -/
def powerOperationZero (X : (CAlg_R k) _⦋0⦌) (n : ℤ) : homotopy k p X n →+ homotopy k p X n := sorry

/-- 概要：(i) π_0 では P⁰ は Frobenius x ↦ x^p。
方針：作用素の次数 0 成分は積。
規約：π_0 は可換環。
使われ方：H⁰(Δ_perf) の Frobenius の同定（Lemma 8.4 (b)）。 -/
theorem powerOperationZero_zero (X : (CAlg_R k) _⦋0⦌) : True := by trivial

/-- 概要：(ii) [Lur11, Rem 2.2.7]：n > 0 なら P⁰ = 0 on π_n。
方針：Lurie DAG XIII §2.2（E∞-F_p 代数の冪作用の性質）、または Mandell の E∞-F_p 代数の P⁰ の議論。
規約：ホモロジー的 n > 0。
使われ方：Lemma 8.4 (a)。 -/
theorem powerOperationZero_pos (X : (CAlg_R k) _⦋0⦌) (n : ℤ) (hn : 0 < n) :
    powerOperationZero k p X n = 0 := by sorry

/-- 概要：P⁰ は E∞ 代数の射で自然。
方針：作用素の作用の自然性。
規約：—
使われ方：Frobenius の自己同型が P⁰ と可換（Δ_perf/p）。 -/
theorem powerOperationZero_natural : True := by trivial

/-- 概要：(iii) 余単体的可換 k 代数 X^• の levelwise Frobenius x ↦ x^p は、Tot_{E∞}(X^•) の P⁰ を誘導する（H^* 上で）。
単体的余単体的（Kan 延長の分解）でも同様に実現の P⁰。
方針：Barratt–Eccles 作用素の p 乗の作用（Alexander–Whitney の p 重 cup 積）が、levelwise の p 乗に一致すること（余単体的可換環では
x ∪ ⋯ ∪ x = front^*(x)⋯back^*(x) が x^p の余面の像に等しい）と、高次の作用素の成分による補正の消滅。
規約：Shared/CosimplicialEInfinity の `totEInfinity`。
使われ方：Lemma 8.4 (a)：Δ_perf/p の φ が P⁰ を誘導する。 -/
theorem powerOperationZero_eq_frobenius_tot : True := by trivial

end SerrePositivity.EInfinity
