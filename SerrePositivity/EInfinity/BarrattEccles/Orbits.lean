module

public import SerrePositivity.EInfinity.BarrattEccles.Nondegenerate

/-!
# 非退化単体の右軌道の代表

概要：Berger–Fresse §1.1 の非退化置換列の自由な Σₙ 軌道を明示する。
方針：先頭頂点の逆元を右乗し、先頭が単位置換である代表を取る。
規約：代表と右乗する置換の順に直積を取る。
使われ方：正規化鎖の次数ごとの自由な群加群基底を構成する。
-/

@[expose] public section

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open scoped Simplicial

/-- 概要：先頭頂点を単位置換にした非退化単体（Berger–Fresse §1.1）。
方針：非退化単体の部分型に先頭の条件を課す。
規約：次数 0 も含める。
使われ方：正規化鎖の群加群としての基底の添字集合になる。 -/
def BasedNondegenerate (n q : ℕ) :=
  {x : (simplicial n).nonDegenerate q // simplexEquiv n q x.val 0 = 1}

/-- 概要：非退化単体を先頭が単位となるように正規化する（Berger–Fresse §1.1）。
方針：先頭頂点の逆元を全ての頂点に右乗する。
規約：非退化性は右作用による保存を用いる。
使われ方：自由軌道の代表を選択なしで取り出す。 -/
def basedRepresentative (n q : ℕ) (x : (simplicial n).nonDegenerate q) :
    BasedNondegenerate n q :=
  ⟨⟨(rightAction n (simplexEquiv n q x.val 0)⁻¹).app _ x.val,
    (rightAction_mem_nonDegenerate_iff _ _ _ _).2 x.property⟩, by simp⟩

/-- 概要：基点つき代表と置換から非退化単体を復元する（Berger–Fresse §1.1）。
方針：代表に置換を右作用させる。
規約：基点つきという条件は出力の非退化性には不要。
使われ方：自由軌道分解の逆写像となる。 -/
def fromBasedRepresentative (n q : ℕ) (x : BasedNondegenerate n q)
    (σ : Equiv.Perm (Fin n)) : (simplicial n).nonDegenerate q :=
  ⟨(rightAction n σ).app _ x.val.val,
    (rightAction_mem_nonDegenerate_iff _ _ _ _).2 x.val.property⟩

/-- 概要：非退化単体は基点つき代表と右作用する置換に一意に分解する（Berger–Fresse §1.1）。
方針：先頭頂点を群成分とし、その逆元で正規化した単体を代表とする。
規約：右作用が積の第二区分だけに作用する分解。
使われ方：Σₙ 上自由な正規化鎖の基底を明示する。 -/
def nondegenerateOrbitEquiv (n q : ℕ) :
    (simplicial n).nonDegenerate q ≃ BasedNondegenerate n q × Equiv.Perm (Fin n) where
  toFun x := (basedRepresentative n q x, simplexEquiv n q x.val 0)
  invFun x := fromBasedRepresentative n q x.1 x.2
  left_inv x := by
    apply Subtype.ext
    apply (simplexEquiv n q).injective
    funext i
    simp [fromBasedRepresentative, basedRepresentative, mul_assoc]
  right_inv x := by
    rcases x with ⟨x, σ⟩
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      apply (simplexEquiv n q).injective
      funext i
      simp [fromBasedRepresentative, basedRepresentative, x.property, mul_assoc]
    · simp [fromBasedRepresentative, x.property]

/-- 概要：自由軌道分解の群成分は先頭の置換である（Berger–Fresse §1.1）。
方針：同値の定義を評価する。
規約：代表の選択に依存しない明示的な成分。
使われ方：群作用の同変性を成分ごとに確認する。 -/
@[simp] lemma nondegenerateOrbitEquiv_snd (n q : ℕ)
    (x : (simplicial n).nonDegenerate q) :
    (nondegenerateOrbitEquiv n q x).2 = simplexEquiv n q x.val 0 := rfl

/-- 概要：自由軌道分解では右作用は群成分だけを変える（Berger–Fresse §1.1）。
方針：先頭頂点による正規化に群の逆元の積の公式を適用する。
規約：部分型の非退化性の証明には右作用の保存を用いる。
使われ方：自由な群加群基底の同変性を与える。 -/
lemma nondegenerateOrbitEquiv_rightAction (n q : ℕ)
    (x : (simplicial n).nonDegenerate q) (σ : Equiv.Perm (Fin n)) :
    nondegenerateOrbitEquiv n q
      ⟨(rightAction n σ).app _ x.val,
        (rightAction_mem_nonDegenerate_iff _ _ _ _).2 x.property⟩ =
      ((nondegenerateOrbitEquiv n q x).1,
        (nondegenerateOrbitEquiv n q x).2 * σ) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    apply (simplexEquiv n q).injective
    funext i
    simp [nondegenerateOrbitEquiv, basedRepresentative, mul_assoc]
  · rfl

end SerrePositivity.EInfinity.BarrattEccles
