module
public import SerrePositivity.KST.SConstruction.ExInfinityPointedEnrichedFunctor

/-! # Ex∞ の全パラメータ族と元の単位
概要：任意の単体集合をパラメータとする族について、包含と単位の厳密回収を与える。
方針：元の全 basedHom 作用へ前合成し、閉 Hom の一般評価式を適用する。
規約：パラメータは頂点に制限しない。使われ方：巨大な Perf 入力の検証の分割。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet

/-- Kan 全 Hom の包含は、元の basedHom 包含と同じ閉 Hom 比較の合成。 -/
lemma exInfinityPointedKan_closed_inclusion (X Y : PointedSSetObject.{u}) :
    exInfinityPointedKanEnrichedFunctor.map X Y ≫
      PointedObject.basedHomι (exInfinityPointedKanEnrichedFunctor.obj X).obj
        (exInfinityPointedKanEnrichedFunctor.obj Y).obj =
    PointedObject.basedHomι X.obj Y.obj ≫
      coaugmentedClosedFamilyMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
        X.obj.right Y.obj.right :=
  exInfinityPointedKanEnrichedFunctor_inclusion X Y

/-- 任意の全族の Ex∞ 像は、包含後に同じ元の閉 Hom 作用を回収する。 -/
lemma exInfinityPointedFamily_inclusion {P : SSet.{u}}
    (X Y : PointedSSetObject.{u}) (a : P ⟶ (X ⟶[SSet.{u}] Y)) :
    (a ≫ exInfinityPointedKanEnrichedFunctor.map X Y) ≫
      PointedObject.basedHomι (exInfinityPointedKanEnrichedFunctor.obj X).obj
        (exInfinityPointedKanEnrichedFunctor.obj Y).obj =
    (a ≫ PointedObject.basedHomι X.obj Y.obj) ≫
      coaugmentedClosedFamilyMap _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
        X.obj.right Y.obj.right := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => a ≫ q) (exInfinityPointedKan_closed_inclusion X Y)).trans
      (Category.assoc _ _ _).symm)

/-- 同じ Ex∞ 単位は、任意のパラメータ全族の実作用に厳密に自然。 -/
lemma exInfinityPointedFamily_unit_action {P : SSet.{u}}
    (X Y : PointedSSetObject.{u}) (a : P ⟶ (X ⟶[SSet.{u}] Y)) :
    ((exInfinityPointedUnit X).right ▷ P) ≫
      uncurry ((a ≫ exInfinityPointedKanEnrichedFunctor.map X Y) ≫
        PointedObject.basedHomι (exInfinityPointedKanEnrichedFunctor.obj X).obj
          (exInfinityPointedKanEnrichedFunctor.obj Y).obj) =
      uncurry (a ≫ PointedObject.basedHomι X.obj Y.obj) ≫
        (exInfinityPointedUnit Y).right := by
  rw [exInfinityPointedFamily_inclusion]
  exact coaugmentedClosedFamilyMap_action _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinityUnit
    (a ≫ PointedObject.basedHomι X.obj Y.obj)

end SerrePositivity.KST.SConstruction
