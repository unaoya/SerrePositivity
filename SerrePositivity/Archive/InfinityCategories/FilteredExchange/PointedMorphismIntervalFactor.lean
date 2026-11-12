module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedValueMorphismIntervalIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：元の canonical 区間値比較を、元の普遍比較と同じ右作用比較の逆の二因子で読む。
方針：元の定義と、指定比較の前合成の合成則を使う。
規約：二因子の指定値を保持。使われ方：元の長辺評価比較の合成。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits

/-- 元の canonical 区間値比較は、同じ指定普遍比較と右作用比較の逆の二因子。 -/
lemma pointedValueMorphismIntervalIso_factor {K L : KanObject.{u}} (f : K ⟶ L) :
    pointedValueMorphismIntervalIso f =
      (pointedIntervalTransportAt_universalIso
        (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge (pointedRightMorphismEdge f)))
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))).postcomp
          (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom ≪≫
        (pointedValueMorphismUniversalActionIso f).symm := by
  rfl

/-- 同じ二因子の指定値は、元の任意の全初期係数による前合成でも保持される。 -/
lemma pointedValueMorphismIntervalIso_precomp_factor {K L : KanObject.{u}} (f : K ⟶ L)
    {C : SSet.{u + 1}} (q : C ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) :
    (pointedValueMorphismIntervalIso f).precomp q =
      ((pointedIntervalTransportAt_universalIso
        (SSet.yonedaEquiv.symm (intervalMappingVertexOfEdge (pointedRightMorphismEdge f)))
        (stdSimplex.obj₀Equiv.symm (0 : Fin 1))).postcomp
          (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom).precomp q ≪≫
        (FunctorIso.precomp (pointedValueMorphismUniversalActionIso f).symm q) := by
  rw [pointedValueMorphismIntervalIso_factor, functorIso_precomp_trans]

end SerrePositivity.InfinityCategories.F2
