module
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedSuspensionTransformation
public import SerrePositivity.KST.SConstruction.ExInfinitySuspensionComparison

/-! # 同じ Ex∞ suspension 比較の厳密単体的自然変換
概要：元の実比較を、全 basedHom に関する厳密豊穣自然変換として与える。
方針：全族自然性を証明した一般の monoidal 単位付き関手に同じ Ex∞ を適用する。
規約：源の suspension 自体に Kan 性を要求しない。使われ方：BF の構造写像の span。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- 元の円・元の単位・同じ Ex∞ の実比較による、厳密単体的 suspension 自然変換。 -/
def exInfinitySuspensionTransformation :
    GradedNatTrans (Center.ofBraidedObj (𝟙_ SSet.{u}))
      (coaugmentedThenSuspensionFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit)
      (suspensionThenCoaugmentedFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit) :=
  coaugmentedPointedSuspensionTransformation _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit

/-- 全 Hom 上の自然変換の成分は、同じ元の Ex∞ suspension 比較そのもの。 -/
lemma exInfinitySuspensionTransformation_app (X : PointedSSetObject.{u}) :
    exInfinitySuspensionTransformation.app X =
      eHomEquiv SSet
        (show (coaugmentedThenSuspensionFunctor
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit).obj X ⟶
          (suspensionThenCoaugmentedFunctor
            _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit).obj X from
              exInfinitySuspensionComparison X) := rfl

end SerrePositivity.KST.SConstruction
