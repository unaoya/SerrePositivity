module
public import SerrePositivity.KST.ProExcision.NonUnitalSimplicialReverse
public import SerrePositivity.KST.ProExcision.RingOppositeComponents
public import SerrePositivity.KST.ProExcision.RingReversalComponents

/-!
# 単位化・反対環・係数反転の実図式比較

概要：非単位環の標準単位化の図式を、反対環と係数方向の rev に自然に移す。
方針：整数単位化の実反対環同型の係数自然性を使う。
規約：KST Proposition 4.14、SW92 §1.2 の非可換な行側比較。
使われ方：反転した係数環の ĜL の成分行列を元の係数環の反対行列環へ送る。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite

/-- 概要：整数単位化の実反対環同型は非単位環準同型に自然。
方針：整数成分と第二成分における単位化の標準拡張の公式を使う。
規約：KST Proposition 4.14、SW92 §1.2。使われ方：実単位化図式の自然同型。 -/
lemma integerUnitizationOpEquiv_natural {I : Type u} {J : Type v} [NonUnitalRing I] [NonUnitalRing J]
    (f : I →ₙ+* J) :
    (integerUnitizationOpEquiv J).toRingHom.comp (integerUnitizationMap (NonUnitalRingHom.op f)) =
      (RingHom.op (integerUnitizationMap f)).comp (integerUnitizationOpEquiv I).toRingHom := by
  apply RingHom.ext
  intro x
  apply MulOpposite.unop_injective
  apply Unitization.ext
  · change (integerUnitizationMap (NonUnitalRingHom.op f) x).fst =
      (integerUnitizationMap f (MulOpposite.unop (integerUnitizationOpEquiv I x))).fst
    rw [integerUnitizationMap_fst, integerUnitizationMap_fst]
    rfl
  · change MulOpposite.unop (integerUnitizationMap (NonUnitalRingHom.op f) x).snd =
      (integerUnitizationMap f (MulOpposite.unop (integerUnitizationOpEquiv I x))).snd
    rw [integerUnitizationMap_snd, integerUnitizationMap_snd]
    rfl

/-- 概要：反対非単位単体環の標準単位化と標準単位化の反対環の実自然同型。
方針：各次数の実環同型を係数準同型への自然性で束ねる。
規約：KST Proposition 4.14。使われ方：非可換な行側の周囲環の実比較。 -/
def NonUnitalSimplicialRing.unitizationOppositeIso (I : NonUnitalSimplicialRing.{u}) :
    I.mulOpposite.standardIdeal.ambient ≅ ringOppositeObject I.standardIdeal.ambient :=
  NatIso.ofComponents (fun k ↦ (integerUnitizationOpEquiv (I.obj k)).toRingCatIso) (by
    intro k l f
    apply RingCat.hom_ext
    exact integerUnitizationOpEquiv_natural (I.map f))

/-- 概要：係数方向を反転した非単位単体環の標準単位化の実比較。
方針：各次数は同じ環であり、面・退化は同じ rev の前合成である。
規約：KST Proposition 4.14。使われ方：成分環の反転同型への接続。 -/
def NonUnitalSimplicialRing.unitizationReverseIso (I : NonUnitalSimplicialRing.{u}) :
    I.reverse.standardIdeal.ambient ≅ SimplicialObject.opFunctor.obj I.standardIdeal.ambient :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- 概要：rev と反対環を施した非単位単体環の標準単位化の実自然同型。
方針：各次数の整数単位化の実反対環同型を、rev した実係数射に適用する。
規約：KST Proposition 4.14、SW92 §1.2 の行側の対角比較。
使われ方：反転と転置の実 ĜL 比較の係数図式。 -/
def NonUnitalSimplicialRing.unitizationReverseOppositeIso (I : NonUnitalSimplicialRing.{u}) :
    I.reverseOpposite.standardIdeal.ambient ≅
      ringOppositeObject (SimplicialObject.opFunctor.obj I.standardIdeal.ambient) :=
  NatIso.ofComponents (fun k ↦ (integerUnitizationOpEquiv (I.obj k)).toRingCatIso) (by
    intro k l f
    apply RingCat.hom_ext
    exact integerUnitizationOpEquiv_natural (I.map (SimplexCategory.rev.map f.unop).op))

end SerrePositivity.KST.ProExcision
