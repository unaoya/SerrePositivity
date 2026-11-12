module

public import SerrePositivity.EInfinity.SimplicialLocalization.KanComparisonNerves
public import SerrePositivity.EInfinity.Hammock.RelativeCompositionPoints
public import SerrePositivity.EInfinity.Hammock.RelativeForwardSimplex
public import SerrePositivity.EInfinity.Hammock.ExInfinityWeakMap
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakWhitehead

/-!
概要：元の相対関手の全 hammock Hom 射を一つの豊穣関手と coherent nerve 射へ束ねる。
方針：元の単位と全合成の保存を使い、同じ Ex∞ で Kan 化する。
規約：点ごとの逆の選択を使わず、元の相対関手と全 Hom 射を保持する。
使われ方：bifibrant 中継から同じ cofibrant 局所化へ戻す全図式比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplicialLocalization
open CategoryTheory Hammock
open SerrePositivity.InfinityCategories
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}}
  (F : LocalizerMorphism C.weakEquivalences D.weakEquivalences)

/-- 概要：同じ相対関手の全 hammock 比較を豊穣関手にする。
方針：全単体における元の単位と合成の保存を適用する。
規約：Hom 射は元の colimitMap。使われ方：元の Kan 化への全族の入力。 -/
def relativeHammockEnriched : EnrichedFunctor SSet.{u} (HammockObjects C) (HammockObjects D) where
  obj X := F.functor.obj X
  map X Y := Relative.colimitMap F X Y
  map_id X := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    cases x
    exact Relative.colimitUnit_point F X n
  map_comp X Y Z := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact Relative.composePoint_map F x.1 x.2

/-- 概要：元の全 hammock 比較を同じ Ex∞ で Kan 化する。
方針：元の豊穣関手へ既存の monoidal 移送を適用する。
規約：元の全合成を保つ。使われ方：同じ coherent nerve 比較。 -/
def relativeKanHammockEnriched :
    EnrichedFunctor SSet.{u} (KanHammockObjects C) (KanHammockObjects D) :=
  exInfinityEnrichedFunctor (relativeHammockEnriched F)

/-- 概要：同じ Kan 豊穣比較を元の通常化された豊穣圏へ送る。
方針：ForgetEnrichment の元の Hom 構造を使う。
規約：同じ Hom 射。使われ方：coherent nerve の型を固定する。 -/
def relativeKanHammockFunctor :
    EnrichedFunctor SSet.{u} (KanHammockCategory C) (KanHammockCategory D) :=
  relativeKanHammockEnriched F

/-- 概要：全図式に一つの実 hammock coherent nerve 比較。
方針：同じ豊穣関手の coherent nerve を取る。
規約：元の相対関手の対象写像。使われ方：局所化普遍性の輸送。 -/
def relativeKanHammockNerve : kanHammockNerve C ⟶ kanHammockNerve D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentNerveMap (relativeKanHammockFunctor F)

/-- 概要：元の Kan 豊穣比較の Hom 射は元の colimitMap の像。
方針：定義を読む。
規約：全 Hom で定義上の一致。使われ方：同じ比較射の弱同値判定。 -/
lemma relativeKanHammockEnriched_map (X Y : KanHammockCategory C) :
    (relativeKanHammockEnriched F).map X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (Relative.colimitMap F X Y) := rfl

/-- 概要：全 Hom の弱同値性は元の coherent nerve 比較の充満忠実性を与える。
方針：同じ Ex∞ の弱同値保存と Kan Whitehead を適用する。
規約：元の全比較を保持。使われ方：包含の全図式の同値判定。 -/
lemma relativeKanHammockNerve_fullyFaithful
    (hF : ∀ X Y, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (Relative.colimitMap F X Y)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (relativeKanHammockNerve F) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.coherentNerveMap_isFullyFaithful_iff (relativeKanHammockFunctor F)).mpr
  intro X Y
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map (Relative.colimitMap F X Y))
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.isWeakHomotopyEquivalence_iff_isQCatEquivalence _).mp
    (exInfinity_map_weak _ (hF X Y))

end SerrePositivity.EInfinity.SimplicialLocalization
