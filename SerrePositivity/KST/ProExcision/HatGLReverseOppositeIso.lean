module
public import SerrePositivity.KST.ProExcision.HatGLReverseOppositeEquiv
public import SerrePositivity.KST.ProExcision.MonoidReverseOpposite

/-!
# 反対転置による ĜL の実単体的同型

概要：非可換な反対転置の各次数の乗法同型を全ての面・退化に自然に束ねる。
方針：整数単位化の反対環同型の自然性を行列の各成分で用いる。
規約：KST Proposition 4.14、SW92 §1.2。係数方向も rev している。
使われ方：非可換な行側の相対 bar 比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite
open scoped Simplicial

/-- 概要：整数単位化の実反対転置は任意の係数準同型に自然。
方針：各行列成分で単位化の実反対環同型の自然性を用いる。
規約：KST Proposition 4.14。使われ方：実 ĜL 比較の全単体射への自然性。 -/
lemma integerUnitizationMatrixOpEquiv_natural
    {J : Type u} {K : Type v} [NonUnitalRing J] [NonUnitalRing K]
    (f : J →ₙ+* K) (n : ℕ)
    (A : Matrix (Fin n) (Fin n) (Unitization ℤ Jᵐᵒᵖ)) :
    integerUnitizationMatrixOpEquiv K n
        ((integerUnitizationMap (NonUnitalRingHom.op f)).mapMatrix A) =
      MulOpposite.op ((integerUnitizationMap f).mapMatrix
        (MulOpposite.unop (integerUnitizationMatrixOpEquiv J n A))) := by
  apply MulOpposite.unop_injective
  apply Matrix.ext
  intro i j
  exact congrArg MulOpposite.unop
    (congrArg (fun h : Unitization ℤ Jᵐᵒᵖ →+* (Unitization ℤ K)ᵐᵒᵖ ↦ h (A j i))
      (integerUnitizationOpEquiv_natural f))

/-- 概要：反対転置の実 ĜL 同型は面・退化と可換。
方針：部分モノイドの外延性により周囲の実行列の係数自然性へ帰着する。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実自然同型の可換性。 -/
lemma NonUnitalSimplicialRing.reverseOppositeHatGL_natural
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) {p q : ℕ} (f : ⦋p⦌ ⟶ ⦋q⦌)
    (A : I.reverseOpposite.hatGLSubmonoid n q) :
    I.reverseOppositeHatGLMulEquiv n p (I.reverseOpposite.hatGLPullback n f A) =
      MonoidHom.op (I.hatGLPullback n (SimplexCategory.rev.map f))
        (I.reverseOppositeHatGLMulEquiv n q A) := by
  apply MulOpposite.unop_injective
  apply Subtype.ext
  exact congrArg MulOpposite.unop
    (integerUnitizationMatrixOpEquiv_natural
      (I.map (SimplexCategory.rev.map f).op) n A.val)

/-- 概要：反転した反対係数環の ĜL と rev した ĜL の反対モノイドの実自然同型。
方針：各次数の実乗法同型を実証明した自然性によって束ねる。
規約：KST Proposition 4.14、SW92 §1.2。単なる係数の転置とは異なる。
使われ方：行側の実対角 bar 比較と列側の零化の移送。 -/
def NonUnitalSimplicialRing.reverseOppositeHatGLIso
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    I.reverseOpposite.hatGL n ≅ monoidReverseOpposite (I.hatGL n) :=
  NatIso.ofComponents (fun k ↦
    (I.reverseOppositeHatGLMulEquiv n k.unop.len).toMonCatIso) (by
      intro k l f
      apply MonCat.hom_ext
      apply MonoidHom.ext
      intro A
      exact I.reverseOppositeHatGL_natural n f.unop A)

end SerrePositivity.KST.ProExcision
