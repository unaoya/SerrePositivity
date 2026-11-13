module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.Opposite
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：反転した標準単体と元の標準単体の join を重みにした edgewise subdivision。
方針：join の両変数の関手性から余単体的重みを作り、重みからの射の前合成を取る。
規約：F1d の Kan 値図式の反転比較の補助構成で、同値性はここでは主張しない。
使われ方：Kerodon Construction 8.1.1.1（Tag 03JG）、Corollary 5.6.0.6（Tag 028T）、自然な反転比較の共通始域。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：edgewise subdivision の余単体的重み Δ[n]op ⋆ Δ[n]。
方針：標準単体の射の反転と元の射を joinMap で同時に写す。
規約：反転は圏の反対ではなく単体集合の頂点順序の反転。
使われ方：Kerodon Construction 8.1.1.1（Tag 03JG）、twisted arrow の重みの関手的表示。 -/
@[kerodon 03JG]
def edgewiseWeight : SimplexCategory ⥤ SSet.{u} where
  obj n := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (stdSimplex.obj n).op (stdSimplex.obj n)
  map α := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map (stdSimplex.map α)) (stdSimplex.map α)
  map_id n := by
    rw [CategoryTheory.Functor.map_id, SSet.opFunctor.map_id, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_id]
  map_comp α β := by
    rw [CategoryTheory.Functor.map_comp, SSet.opFunctor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]

/-- 概要：単体集合 X の edgewise subdivision。
方針：n 単体を Δ[n]op ⋆ Δ[n] から X への射とし、重みの射で前合成する。
規約：次数 n の射の型を直接使い、宇宙を持ち上げない。
使われ方：Kerodon Construction 8.1.1.1（Tag 03JG）、Kan 複体とその反転を比較する中間単体集合。 -/
@[kerodon 03JG]
def edgewiseSubdivision (X : SSet.{u}) : SSet.{u} where
  obj n := edgewiseWeight.obj n.unop ⟶ X
  map α := ↾fun f ↦ edgewiseWeight.map α.unop ≫ f
  map_id n := by
    apply ConcreteCategory.hom_ext
    intro f
    change edgewiseWeight.map (𝟙 n.unop) ≫ f = f
    rw [edgewiseWeight.map_id, Category.id_comp]
  map_comp α β := by
    apply ConcreteCategory.hom_ext
    intro f
    change edgewiseWeight.map (β.unop ≫ α.unop) ≫ f =
      edgewiseWeight.map β.unop ≫ (edgewiseWeight.map α.unop ≫ f)
    rw [edgewiseWeight.map_comp, Category.assoc]

/-- 概要：単体集合の射による edgewise subdivision の後合成。
方針：重みからの射に通常の後合成を施す。
規約：定義に Kan 性は要求しない。
使われ方：Kerodon Remark 8.1.1.4（Tag 00B3）、図式の各対象で自然な反転比較を作る。 -/
def edgewiseSubdivisionMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    edgewiseSubdivision X ⟶ edgewiseSubdivision Y where
  app _ := ↾fun g ↦ g ≫ f
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro g
    change (edgewiseWeight.map α.unop ≫ g) ≫ f =
      edgewiseWeight.map α.unop ≫ (g ≫ f)
    exact Category.assoc _ _ _

/-- 概要：edgewise subdivision は単体集合の通常の圏の自己関手。
方針：後合成の恒等則と結合則を各次数で使う。
規約：極限・余極限についての主張は含めない。
使われ方：Kerodon Remark 8.1.1.4（Tag 00B3）、Kan 値図式の比較の自然性。 -/
def edgewiseSubdivisionFunctor : SSet.{u} ⥤ SSet.{u} where
  obj := edgewiseSubdivision
  map := edgewiseSubdivisionMap
  map_id X := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro f
    exact Category.comp_id f
  map_comp f g := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro h
    exact (Category.assoc h f g).symm

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "5.2.1.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision
attribute [cite HA "5.2.1.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight
