module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentCompositionEndpointHom
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.WeightedTriangleLongHom

/-!
概要：実終点円柱の長辺 Hom は標準 weighted cone の同じ全次数の Hom。
方針：両辺を同じ元の指定精密化の Yoneda 射へ戻す。
規約：係数の始点と終点を元の三角形の対象に固定する。
使われ方：実 coslice 終点辺と標準 Hom 比較の全三角形の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 実終点円柱の長辺 Hom と標準反転 Hom 比較の長辺 Hom の全次数での一致。 -/
lemma coherentCompositionEndpoint_hom_zero_two_weighted
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (s : (SimplicialNerve C) _⦋2⦌) :
    (coherentPrefixConeSimplex (coherentCompositionTetrahedron s)
      (OrderHom.const (Fin 2) (2 : Fin 3)) (OrderHom.id (α := Fin 2))).map
        ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ =
      weightedConeHom ((Functor.const (Discrete PUnit.{u + 1})).obj (s.obj ⟨ULift.up 2⟩))
        (s.obj ⟨ULift.up 0⟩)
        (weightedNerveConstantDiagram
          (simplicialHomDiagram
            ((Functor.const (Discrete PUnit.{u + 1})).obj (s.obj ⟨ULift.up 2⟩))
            (s.obj ⟨ULift.up 0⟩) ⋙ SSet.opFunctor)
          ⟨PUnit.unit⟩ (SSet.opObjEquiv.symm (coherentTriangleHomotopy s))) 0 2 := by
  rw [coherentCompositionEndpoint_hom_zero_two, weightedTriangleLongHom]
  rfl

end SerrePositivity.InfinityCategories.F2
