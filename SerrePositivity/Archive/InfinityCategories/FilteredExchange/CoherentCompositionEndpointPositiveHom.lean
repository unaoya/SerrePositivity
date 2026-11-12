module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentCompositionEndpointHom
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FlagEquiv
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.WeightedConstantFiber

/-!
概要：実終点三角形と定値 weighted cone の正頂点間の Hom は同じ豊穣恒等。
方針：実作用を元の対象の自己 Hom に戻し、定値図式の恒等射を計算する。
規約：逆向きで空な Hom も含めた全次数の射として比較する。
使われ方：実 coslice 辺と標準反転 Hom 比較の全三角形の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet SemiCartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 実終点円柱の全ての正頂点間の Hom は元の終点対象の豊穣恒等に定値。 -/
lemma coherentCompositionEndpoint_hom_positive
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) (i j : Fin 2) :
    (coherentPrefixConeSimplex (coherentCompositionTetrahedron s)
      (OrderHom.const (Fin 2) (2 : Fin 3)) (OrderHom.id (α := Fin 2))).map
        ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ =
      toUnit _ ≫ eId SSet (s.obj ⟨ULift.up 2⟩) := by
  have hs := enrichedFunctor_thickening_self_map s (ULift.up (2 : Fin 3)) rfl
  simp only [eqToHom_refl, Category.comp_id] at hs
  change nerveMap _ ≫ nerveMap _ ≫ s.map ⟨ULift.up 2⟩ ⟨ULift.up 2⟩ = _
  simp only [hs, ← Category.assoc]
  congr 1

/-- 定値 weighted cone の全ての正頂点間の Hom は同じ対象の豊穣恒等に定値。 -/
lemma weightedTrianglePositiveHom
    {C : Type v} [Category.{u} C] [SimplicialCategory C] (x y : C)
    (s : (SimplicialCategory.sHom x y).op _⦋1⦌) (i j : Fin 2) :
    weightedConeHom ((Functor.const (Discrete PUnit.{u + 1})).obj y) x
      (weightedNerveConstantDiagram
        (simplicialHomDiagram ((Functor.const (Discrete PUnit.{u + 1})).obj y) x ⋙
          SSet.opFunctor) ⟨PUnit.unit⟩ s) i.succ j.succ = toUnit _ ≫ eId SSet y := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  change PinchedHom.constant (SimplicialCategory.homEquiv' y y (𝟙 y)) d =
    (eId SSet y).app (Opposite.op ⦋d⦌) PUnit.unit
  simp only [SimplicialCategory.homEquiv', Equiv.trans_apply, eHomEquiv_id]
  exact (unitHom_app_constant (eId SSet y) d).symm

end SerrePositivity.InfinityCategories.F2
