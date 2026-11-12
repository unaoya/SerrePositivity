module
public import SerrePositivity.KST.SConstruction.ExInfinitySuspensionComparison
public import SerrePositivity.KST.SConstruction.CoaugmentedPointedFunctorialMaps

/-! # 同じ Ex∞ suspension 右脚と元の組み立ての単位による回収
概要：前向き比較と写した射の合成が、元の suspension 単位上で同じ元の射を回収する。
方針：元の比較の単位条件と、同じ点つき単位の自然性を合成する。
規約：逆射や単射性は使わない。使われ方：元の BF 構造射との比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet

/-- 比較と元の射の Ex∞ 像の合成は、元の単位上で同じ元の射を厳密に回収する。 -/
lemma exInfinitySuspensionAssembly_unit {X Y : PointedSSetObject.{u}}
    (f : pointedSSetSuspensionObject X ⟶ Y) :
    exInfinitySuspensionUnit X ≫
      (exInfinitySuspensionComparison X ≫ (exInfinityPointedKanMap f).hom) =
    (show (pointedSSetSuspensionObject X).obj ⟶ Y.obj from f) ≫
      exInfinityPointedUnit Y := by
  rw [← Category.assoc, exInfinitySuspensionComparison_unit]
  exact coaugmentedPointedUnit_naturality _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit f

end SerrePositivity.KST.SConstruction
