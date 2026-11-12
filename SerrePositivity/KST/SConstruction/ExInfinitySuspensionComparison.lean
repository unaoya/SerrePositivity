module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedSuspensionNaturality
public import SerrePositivity.KST.SConstruction.ExInfinityPointedEnrichedFunctor

/-! # 同じ Ex∞ と元の円による suspension 比較
概要：元の点つき Kan 置換の値を使い、ΣEx∞X から Ex∞ΣX への実比較を与える。
方針：有限積保存による元の smash 比較に、元の円の Ex∞ 単位を前合成する。
規約：単射性や厳密な逆を追加仮定しない。使われ方：元の BF 構造射の前向き span。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- 元の同じ Ex∞ Kan 値の suspension から、元の suspension の Ex∞ Kan 値への実比較。 -/
def exInfinitySuspensionComparison (X : PointedSSetObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (exInfinityPointedKanEnrichedFunctor.obj X).obj ⟶
      (exInfinityPointedKanEnrichedFunctor.obj (pointedSSetSuspensionObject X)).obj :=
  coaugmentedPointedSuspensionComparison _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit X

/-- 元の円を固定した、同じ Ex∞ 単位の suspension。 -/
def exInfinitySuspensionUnit (X : PointedSSetObject.{u}) :
    _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X.obj ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (exInfinityPointedKanEnrichedFunctor.obj X).obj :=
  coaugmentedPointedSuspensionUnit _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit X

/-- 元の直積商射上で、円の単位・Ex∞ の乗法比較・元の商射の像を厳密に回収する。 -/
lemma exInfinitySuspensionComparison_quotient (X : PointedSSetObject.{u}) :
    PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u}
      (exInfinityPointedKanEnrichedFunctor.obj X).obj ≫
      (exInfinitySuspensionComparison X).right =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit.app PointedSimplicialSet.circle.{u}.right ⊗ₘ
      𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.obj X.obj.right)) ≫
      Functor.LaxMonoidal.μ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity PointedSimplicialSet.circle.{u}.right
        X.obj.right ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map
          (PointedSimplicialSet.productToSmash PointedSimplicialSet.circle.{u} X.obj) :=
  coaugmentedPointedSuspensionComparison_quotient
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit X

/-- 同じ単位の suspension と比較の合成は、元の suspension の同じ Ex∞ 単位を回収する。 -/
lemma exInfinitySuspensionComparison_unit (X : PointedSSetObject.{u}) :
    exInfinitySuspensionUnit X ≫ exInfinitySuspensionComparison X =
      exInfinityPointedUnit (pointedSSetSuspensionObject X) :=
  coaugmentedPointedSuspensionComparison_unit _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit X

/-- 同じ Ex∞ suspension 比較は、元の通常の点つき射について厳密に自然。 -/
lemma exInfinitySuspensionComparison_naturality {X Y : PointedSSetObject.{u}} (f : X ⟶ Y) :
    (PointedSimplicialSet.circle.{u} ◁ (exInfinityPointedKanMap f).hom) ≫
      exInfinitySuspensionComparison Y =
    exInfinitySuspensionComparison X ≫
      (exInfinityPointedKanMap (pointedSSetSuspensionMap f)).hom :=
  coaugmentedPointedSuspensionComparison_naturality
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit f

end SerrePositivity.KST.SConstruction
