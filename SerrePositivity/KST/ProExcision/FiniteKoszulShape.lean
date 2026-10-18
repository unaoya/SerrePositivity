module

public import SerrePositivity.KST.ProExcision.KoszulCoefficients
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

/-!
# 有限 Koszul 行の複体形状

概要：係数次数を固定した有限の初頁の行を、一つの有限複体として取り出す。
方針：有限下降形状を整数次数と補助初頁の形状へ埋め込み、閉じた埋め込みのホモロジーを比較する。
規約：上端・下端に存在しない微分を循環する微分で置き換えない。
使われ方：KST Lemma 4.10 の次頁の Koszul ホモロジー同定。
-/

universe u v w

namespace SerrePositivity.KST.ProExcision

open CategoryTheory CategoryTheory.Limits HomologicalComplex

/-- 概要：長さ e の Koszul 複体の有限下降形状。
方針：自然数の値が一つ減るときだけ微分を許す。
規約：Fin の巡回加法は使用しない。使われ方：KST Lemma 4.10 の有限初頁の一行。 -/
def finiteKoszulShape (e : ℕ) : ComplexShape (Fin (e + 1)) where
  Rel i j := j.val + 1 = i.val
  next_eq h h' := Fin.ext (by omega)
  prev_eq h h' := Fin.ext (by omega)

/-- 概要：有限 Koszul 行をコホモロジー整数次数へ埋め込む。
方針：行 p を -p 次へ送る。
規約：微分の向きは上昇。使われ方：KST Lemma 4.10 の Koszul 複体との比較。 -/
def finiteKoszulIntEmbedding (e : ℕ) : (finiteKoszulShape e).Embedding (.up ℤ) where
  f p := -(p.val : ℤ)
  injective_f {p q} h := Fin.ext (Int.ofNat_inj.mp (neg_injective h))
  rel {i j} h := by
    change j.val + 1 = i.val at h
    change -(i.val : ℤ) + 1 = -(j.val : ℤ)
    omega

/-- 概要：整数次数への埋め込みは微分関係を反映する。
方針：整数の等式を有限行の値の等式へ戻す。
規約：両端を含む。使われ方：KST Lemma 4.10 の複体の制限。 -/
instance finiteKoszulIntEmbedding_isRelIff (e : ℕ) :
    (finiteKoszulIntEmbedding e).IsRelIff where
  rel' i j h := by
    change -(i.val : ℤ) + 1 = -(j.val : ℤ) at h
    change j.val + 1 = i.val
    omega

/-- 概要：係数次数 t を固定した有限行を補助初頁へ埋め込む。
方針：行 p を位置 (t-2p,p) へ送る。
規約：補助頁は Mathlib の頁 2。使われ方：KST Lemma 4.10 の E₂ 計算。 -/
def finiteKoszulSpectralEmbedding (e : ℕ) (t : ℤ) :
    (finiteKoszulShape e).Embedding (ComplexShape.spectralSequenceFin (e + 1) (2, -1)) where
  f p := (t - 2 * (p.val : ℤ), p)
  injective_f {_ _} h := congrArg Prod.snd h
  rel {i j} h := by
    change j.val + 1 = i.val at h
    change (t - 2 * (i.val : ℤ)) + 2 = t - 2 * (j.val : ℤ) ∧
      (i.val : ℤ) + (-1) = (j.val : ℤ)
    constructor <;> omega

/-- 概要：補助初頁への固定係数次数の埋め込みは微分関係を反映する。
方針：微分の第二座標の等式を使う。
規約：係数次数は不変。使われ方：KST Lemma 4.10 の有限行への制限。 -/
instance finiteKoszulSpectralEmbedding_isRelIff (e : ℕ) (t : ℤ) :
    (finiteKoszulSpectralEmbedding e t).IsRelIff where
  rel' i j h := by
    change (t - 2 * (i.val : ℤ)) + 2 = t - 2 * (j.val : ℤ) ∧
      (i.val : ℤ) + (-1) = (j.val : ℤ) at h
    change j.val + 1 = i.val
    omega

/-- 概要：固定係数次数の有限行の像は次の微分先について閉じる。
方針：微分の二座標の等式から係数次数の不変性を計算する。
規約：微分先がある場合のみ。使われ方：KST Lemma 4.10 の下端のホモロジー比較。 -/
instance finiteKoszulSpectralEmbedding_isTruncGE (e : ℕ) (t : ℤ) :
    (finiteKoszulSpectralEmbedding e t).IsTruncGE where
  mem_next {j k'} h := by
    refine ⟨k'.2, ?_⟩
    apply Prod.ext
    · change (t - 2 * (j.val : ℤ)) + 2 = k'.1 ∧
        (j.val : ℤ) + (-1) = (k'.2.val : ℤ) at h
      change t - 2 * (k'.2.val : ℤ) = k'.1
      omega
    · rfl

/-- 概要：固定係数次数の有限行の像は前の微分元について閉じる。
方針：微分の二座標の等式から同じ係数次数を回復する。
規約：微分元がある場合のみ。使われ方：KST Lemma 4.10 の上端のホモロジー比較。 -/
instance finiteKoszulSpectralEmbedding_isTruncLE (e : ℕ) (t : ℤ) :
    (finiteKoszulSpectralEmbedding e t).IsTruncLE where
  mem_prev {i' j} h := by
    refine ⟨i'.2, ?_⟩
    apply Prod.ext
    · change i'.1 + 2 = t - 2 * (j.val : ℤ) ∧
        (i'.2.val : ℤ) + (-1) = (j.val : ℤ) at h
      change t - 2 * (i'.2.val : ℤ) = i'.1
      omega
    · rfl

/-- 概要：前向きに閉じた複体形状の埋め込みは次添字と可換。
方針：微分先がある場合は一意性、ない場合は像の閉性で比較する。
規約：微分先のない端では自身を次添字とする Mathlib 規約を使う。
使われ方：KST Lemma 4.10 の制限複体のホモロジー。 -/
theorem closedEmbedding_next {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J}
    (e : c.Embedding c') [e.IsTruncGE] (p : I) : e.f (c.next p) = c'.next (e.f p) := by
  by_cases h : c.Rel p (c.next p)
  · exact (c'.next_eq' (e.rel h)).symm
  · rw [c.next_eq_self p h]
    symm
    apply c'.next_eq_self'
    intro k' hk'
    obtain ⟨k, rfl⟩ := e.mem_next hk'
    have hk := (e.rel_iff p k).mp hk'
    exact h (by simpa only [c.next_eq' hk] using hk)

/-- 概要：後ろ向きに閉じた複体形状の埋め込みは前添字と可換。
方針：微分元の存在で分け、像の閉性と一意性を使う。
規約：端での自身への添字規約を含む。使われ方：KST Lemma 4.10 の制限ホモロジー。 -/
theorem closedEmbedding_prev {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J}
    (e : c.Embedding c') [e.IsTruncLE] (p : I) : e.f (c.prev p) = c'.prev (e.f p) := by
  by_cases h : c.Rel (c.prev p) p
  · exact (c'.prev_eq' (e.rel h)).symm
  · rw [c.prev_eq_self p h]
    symm
    apply c'.prev_eq_self'
    intro i' hi'
    obtain ⟨i, rfl⟩ := e.mem_prev hi'
    have hi := (e.rel_iff i p).mp hi'
    exact h (by simpa only [c.prev_eq' hi] using hi)

/-- 概要：両方向に閉じた形状の埋め込みへの制限は、対応する次数のホモロジーを保つ。
方針：前添字と次添字の可換性を既存の制限ホモロジー同型へ渡す。
規約：端の例外を含む。使われ方：KST Lemma 4.10 の有限初頁の各行のホモロジー。 -/
def closedRestrictionHomologyIso
    {I J : Type*} {c : ComplexShape I} {c' : ComplexShape J}
    {C : Type v} [Category.{w} C] [Abelian C]
    (K : HomologicalComplex C c') (e : c.Embedding c') [e.IsTruncGE] [e.IsTruncLE] (p : I) :
    (K.restriction e).homology p ≅ K.homology (e.f p) :=
  K.restrictionHomologyIso e (c.prev p) p (c.next p) rfl rfl rfl rfl rfl
    (closedEmbedding_prev e p).symm (closedEmbedding_next e p).symm

end SerrePositivity.KST.ProExcision
