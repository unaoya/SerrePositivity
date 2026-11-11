module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionReverse
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanPointHomActionIso
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeInternalHomEvaluation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseInternalHom

/-!
概要：反対の Kan 圏における一点 Hom の反転合成作用を内部 Hom の同型として表示する。
方針：合成作用を curry し、ULift と反転の内部 Hom 比較へ分解する。
規約：実際の coherentReverseHomComposition の作用を扱う。
使われ方：普遍 coslice 輸送の写像空間上の同値性への標準作用側の入力。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：反対 Kan 圏の一点 Hom の反転合成は標準作用と ULift・反転比較の合成。
方針：展開して二つの内部 Hom 比較の評価公式を使い、残る直積の交換を計算する。
規約：写像空間と係数の宇宙は coherent nerve に合わせて持ち上げる。
使われ方：標準反転合成作用の同型性。 -/
lemma coherentReversePointHomAction_eq (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    curry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
      (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject)) =
    SSet.opFunctor.map ((SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanPointHomEnriched.map K L)) ≫
      SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftInternalHomComparison
        (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K) (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject L)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.OppositeInternalHom.oppositeInternalHomIso
        ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K))
        ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject L))).hom := by
  apply uncurry_injective
  rw [uncurry_curry, ← Category.assoc, ← SSet.opFunctor.map_comp,
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.oppositeInternalHom_map_uncurry]
  have hu := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.uliftInternalHomComparison_map_uncurry.{u, u + 1}
    (K := SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K)
    (B := SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject L)
    (show SimplicialCategory.sHom K L ⟶
      (ihom (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K)).obj
        (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject L) from _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanPointHomEnriched.map K L)
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso
        ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject K))
        ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))).hom ≫
      SSet.opFunctor.map ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso _ _).inv ≫
        (SSet.uliftFunctor.{u + 1, u}).map (uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanPointHomEnriched.map K L))) := by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    _ = _ := congrArg (fun f ↦ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.opTensorIso _ _).hom ≫ SSet.opFunctor.map f) hu.symm

/-- 概要：反転した一点 Hom の豊穣合成の curry は厳密な同型。
方針：一点 Hom の標準作用と ULift・反転の同型の合成へ移す。
規約：元の合成作用そのものについての同型性。
使われ方：標準輸送の作用が普遍輸送の同値性を検出する。 -/
instance coherentReversePointHomAction_isIso (K L : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    IsIso (curry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentReverseHomComposition (Opposite.op L) (Opposite.op K)
      (Opposite.op _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject))) := by
  rw [coherentReversePointHomAction_eq]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
