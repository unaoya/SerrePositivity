module

public import SerrePositivity.EInfinity.Hammock.AsSmallComposition
public import SerrePositivity.EInfinity.FrameHom.KanHomFamily
public import SerrePositivity.EInfinity.FrameHom.SourceRoofFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNaturalTransformation

/-!
概要：元の全標的 hammock Hom 図式を同じ AsSmall 表示に全自然に同定する。
方針：元の宇宙同型の合成保存を全自然性として使い、同じ Ex∞ へ送る。
規約：一つの実自然変換を構成してから coherent な比較にする。
使われ方：right frame 比較の終端と同じ Kan hammock 豊穣 Hom 図式の整合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet Hammock
open SerrePositivity.InfinityCategories
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative] (X : C)

/-- 概要：元の全 Hom 族の AsSmall 表示への同じ実自然同型。
方針：同じ各余極限同型と全後合成の可換式を使う。
規約：全標的・全射を保持。使われ方：同じ Kan 図式の宇宙比較。 -/
def asSmallHammockHomFamilyIso :
    AsSmall.down ⋙ hammockHomFamily W X ≅
      hammockHomFamily (AsSmallComparison.weak W) (AsSmall.up.obj X) :=
  NatIso.ofComponents (fun Y => AsSmallComparison.colimitIso W X (AsSmall.down.obj Y))
    (by intro Y Z f; exact AsSmallComparison.colimitIso_postcompose W (AsSmall.down.map f))

/-- 概要：同じ実全自然同型を同じ Ex∞ の Kan 図式間の自然変換へ送る。
方針：元の全射へ一つの関手を適用する。
規約：元の同型成分そのもの。使われ方：coherent 図式同型への実入力。 -/
def asSmallKanHammockHomFamilyMap :
    AsSmall.down ⋙ kanHomFamily (hammockHomFamily W X) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget ⟶
      kanHomFamily (hammockHomFamily (AsSmallComparison.weak W) (AsSmall.up.obj X)) ⋙
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget :=
  Functor.whiskerRight (asSmallHammockHomFamilyIso W X).hom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity

/-- 概要：同じ Kan 自然変換の全成分は実際の同型。
方針：同じ余極限の実同型を Ex∞ に写す。
規約：元の射を保持。使われ方：全図式の反転。 -/
lemma asSmallKanHammockHomFamilyMap_isIso (Y : AsSmall.{max u v} C) :
    IsIso ((asSmallKanHammockHomFamilyMap W X).app Y) := by
  change IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.map ((asSmallHammockHomFamilyIso W X).hom.app Y))
  infer_instance

attribute [local instance] kanHomFamily_kanComplex

/-- 概要：同じ AsSmall 全自然変換は coherent な全 Hom 図式の同型を与える。
方針：実自然変換を構成したうえで、その同じ同型成分を全図式の反転へ渡す。
規約：点ごとの同値だけから図式同型を推論しない。
使われ方：S (6) の終端と同じ balanced Kan hammock Hom 図式の比較。
-/
def asSmallHammockHomCoherentIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (AsSmall.down ⋙ kanHomFamily (hammockHomFamily W X)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
        (kanHomFamily (hammockHomFamily (AsSmallComparison.weak W) (AsSmall.up.obj X)))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramFunctorIsoOfPointwise
    (F := ⟨AsSmall.down ⋙ kanHomFamily (hammockHomFamily W X), trivial⟩)
    (G := ⟨kanHomFamily (hammockHomFamily (AsSmallComparison.weak W)
      (AsSmall.up.obj X)), trivial⟩)
    (asSmallKanHammockHomFamilyMap W X) (fun Y => by
      let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.exInfinity.mapIso ((asSmallHammockHomFamilyIso W X).app Y))
      exact e.isQCatEquivalence)

end SerrePositivity.EInfinity.FrameHom
