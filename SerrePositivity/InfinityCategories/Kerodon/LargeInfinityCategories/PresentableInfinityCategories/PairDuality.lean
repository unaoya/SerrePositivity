module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairHomFamilyFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PairAdjointFunctorMeaning
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UniverseFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-!
概要：presentable 二対象の元の全随伴関手 ∞ 圏の反変双対。
方針：全単位族の充満忠実性を共変 Yoneda から回収し、同じ射の本質的全射性と合わせる。
規約：非可逆変換を含む元の PrLFunctorSpace と PrRFunctorSpace の反対を使う。
使われ方：対ごとの随伴対応の公開界面。全体の Pr の合成との整合は別の工程に残す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の全関手圏間の実際の反変随伴選択は充満忠実。
方針：全単位族との全自然な Yoneda 比較から回収し、同じ単体射の宇宙持ち上げを降ろす。
規約：元の反変射の Hom 作用を保持する。
使われ方：対ごとの全同値の判定。 -/
lemma pairRightAdjointFunctor_isFullyFaithful (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightAdjointFunctor C D) := by
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightAdjointFunctorLifted C D ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairCovariantYoneda (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C)) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorIso.isFullyFaithful_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightAdjointFunctorLifted_yonedaIso C D)).mpr
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairUnitHomFamily_isFullyFaithful C D)
  have hf := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairCovariantYoneda_isFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C)).cancel_right hc
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fullyFaithful_of_ulift.{u + 1, u + 2}
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightAdjointFunctor_ulift] using hf

/-- 概要：元の全関手圏間の同じ反変随伴選択は QCat 同値。
方針：構成した同じ射の充満忠実性と本質的全射性を合わせる。
規約：core の同値ではなく全関手圏の同値。
使われ方：逆射と両往復の関手同型を持つ公開同値の構成。 -/
lemma pairRightAdjointFunctor_isQCatEquivalence (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightAdjointFunctor C D) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightAdjointFunctor C D) (pairRightAdjointFunctor_isFullyFaithful C D)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightAdjointFunctor_isEssentiallySurjective C D)

/-- 概要：presentable 二対象の全左随伴関手圏と反対全右随伴関手圏の同値。
方針：元の全単位族から作った同じ反変随伴射の逆と両往復同型を選ぶ。
規約：非可逆変換と全高次単体を含む。全体の Pr の同値は主張しない。
使われ方：対ごとの随伴双対性の主公開名。 -/
def presentableAdjointFunctorEquivalence (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrRFunctorSpace D C).op :=
  (pairRightAdjointFunctor_isQCatEquivalence C D).choose

/-- 概要：公開同値の順方向は構成した元の反変随伴射そのもの。
方針：同値の選択で順方向を保持する定義を使う。
規約：単体射の厳密な等式。
使われ方：既存の頂点・随伴比較の直接利用。 -/
lemma presentableAdjointFunctorEquivalence_hom (C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}) :
    (presentableAdjointFunctorEquivalence C D).hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightAdjointFunctor C D := rfl

/-- 概要：公開同値の各右関手値は元の左関手の実際の右随伴。
方針：同じ順方向の射について構成済みの随伴を使う。
規約：元の左関手と同じ同値の値を保持する。
使われ方：公開同値を随伴対応として消費する。 -/
def presentableAdjointFunctorEquivalence_adjunction {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableInfinityObject.{u}}
    (v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PrLFunctorSpace C D _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.leftVertexFunctor v)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.rightVertexFunctor (SSet.opObjEquiv
        ((presentableAdjointFunctorEquivalence C D).hom.app (Opposite.op ⦋0⦌) v))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pairRightAdjointFunctorAdjunction v

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.2.6.2" (partial := stronger-hyp) "仮定：C,D が presentable（Lean が強い：任意の準圏の場合は含まない）。結論：FunL(C,D) と FunR(D,C)op の全準圏の同値で、同値の順方向の各値は元の左関手の右随伴（この場合に一致）。PrL/PrR の頂点条件と随伴存在の同値も併用する。非可逆な自然変換と全高次単体を保持し、右随伴の対象ごとの選択だけでは代用しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableAdjointFunctorEquivalence
attribute [cite HTT "5.2.6.2" (partial := stronger-hyp) "仮定：C,D が presentable（Lean が強い：任意の準圏の場合は含まない）。結論：FunL(C,D) と FunR(D,C)op の全準圏の同値で、同値の順方向の各値は元の左関手の右随伴（この場合に一致）。PrL/PrR の頂点条件と随伴存在の同値も併用する。非可逆な自然変換と全高次単体を保持し、右随伴の対象ごとの選択だけでは代用しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.presentableAdjointFunctorEquivalence_adjunction
