module

public import SerrePositivity.CLMST.Almost

/-! # mod p^N の perfectoid ideal の冪等性（文献入力）

CLMST arXiv:2209.04046v4, §2.4、Lemma 2.4.3 の直前の段落は、
有限生成イデアル J の perfectoid 化の像について、各 n で
`(R/p^n, J_perfd R/p^n)` が almost 理論の basic setup を与えると述べる。
ここではその冪等性の成分だけを引用する。平坦性等の全条件を証明したとはしない。

同じ冪等性は Bhatt–Scholze, *Prisms and prismatic cohomology*,
§10.1, Remark 10.7 にも明記されている。Lemma 2.4.3 の根生成イデアルとの比較には
compatible な p 冪根と p 進閉包が必要だが、この引用は任意の g に適用する。
本実装では普遍性で選んだ perfectoid 化への写像の核を使用する。

出典：https://arxiv.org/html/2209.04046v4 （§2.4、Lemma 2.4.3 の直前）、
https://arxiv.org/pdf/1905.08229 （Remark 10.7）。
-/

public section
universe u
namespace SerrePositivity.CLMST.Inputs

/-- perfectoid 環 R の任意の元 g について、mod p^N の perfectoid ideal の像は冪等。
P：CLMST §2.4 の basic setup の主張の冪等性成分、Bhatt–Scholze Remark 10.7。
g の非零性・根の選択・整域性・Noether 性は要求しない。
N=0 は零環の初等的な場合として証明し、正の指数の成分を文献入力とする。 -/
theorem perfectoidIdealMod_idempotent
    (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p) (g : R) (N : ℕ) :
    perfectoidIdealMod R p hR g N * perfectoidIdealMod R p hR g N =
      perfectoidIdealMod R p hR g N := by
  cases N with
  | zero =>
    have htop : Ideal.span {(p : R) ^ 0} = ⊤ := by simp
    have : Subsingleton (R ⧸ Ideal.span {(p : R) ^ 0}) := by
      rw [htop]
      infer_instance
    exact Subsingleton.elim _ _
  | succ N =>
    sorry

end SerrePositivity.CLMST.Inputs
