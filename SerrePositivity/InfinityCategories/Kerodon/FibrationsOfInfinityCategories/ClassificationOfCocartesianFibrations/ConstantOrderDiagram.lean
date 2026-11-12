module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices

/-!
概要：順序の thickening からの定値な豊穣図式と coherent 頂点の定値単体。
方針：全 Hom を単位を介して恒等へ写し、coherent nerve の定値単体との一致を示す。
規約：対象の局所 Kan 性は不要。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類関手を fibration の頂点に制限する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：単体的圏の対象を任意の順序の thickening 上の定値図式にする。
方針：全ての豊穣 Hom を単位からの恒等射へ写す。
規約：J は対象の Hom と同じ宇宙 u の順序。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、coherent なパラメーターを頂点に固定する。 -/
noncomputable def enrichedConstantOrderDiagram (J : Type u) [LinearOrder J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (c : C) :
    EnrichedFunctor SSet.{u} (SimplicialThickening J) C where
  obj _ := c
  map i j := toUnit _ ≫ eId SSet c
  map_id i := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  map_comp i j k := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app (e_id_comp SSet c c) n)
      ((eId SSet c).app n PUnit.unit)).symm

/-- 概要：coherent nerve の標準頂点の定値単体は定値な豊穣順序図式に一致する。
方針：対象の作用と全 Hom の単位を経由する式を各次数で比較する。
規約：n は任意の次数。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、共同評価の fibration パラメーターを固定する。 -/
lemma coherentNerveVertex_constant {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (c : C) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex c) n =
      enrichedConstantOrderDiagram (ULift.{u} (Fin (n + 1))) c := by
  refine EnrichedFunctor.ext SSet
    (F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex c) n)
    (G := enrichedConstantOrderDiagram (ULift.{u} (Fin (n + 1))) c) (fun _ ↦ rfl) ?_
  intro i j
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  rfl

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
