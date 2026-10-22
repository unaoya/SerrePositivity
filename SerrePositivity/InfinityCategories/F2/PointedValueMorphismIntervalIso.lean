module

public import SerrePositivity.InfinityCategories.F2.PointedIntervalTransportAtUniversalIso
public import SerrePositivity.InfinityCategories.F2.PointedValueMorphismUniversalAction

/-!
概要：元の Kan 射の同じ区間頂点による実輸送を、元の値射と Kan 射の合成へ比較する。
方針：元の全輸送比較の指定点成分と、元の全 Hom の同じ指定成分を合成する。
規約：辺・指定点・二比較を保持。使われ方：普遍三角形残余の値を元の精密化へ戻す。
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
variable {K L : KanObject.{u}} (f : K ⟶ L)
local notation "v" => intervalMappingVertexOfEdge (pointedRightMorphismEdge f)
local notation "a" => SSet.yonedaEquiv.symm v
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "W" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L))

/-- 元の Kan 射の同じ零単体区間による実輸送は、同じ二指定成分で元の Kan 射に比較される。 -/
def pointedValueMorphismIntervalIso :
    FunctorIso (pointedIntervalTransportAt a l ≫ W)
      ((pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map f) := by
  have hv : (NatTrans.app a (Opposite.op ⦋0⦌)) l = v := by
    rw [SSet.yonedaEquiv_symm_zero]
    rfl
  have he := pointedIntervalTransportAt_universalIso a l
  rw [hv] at he
  exact (he.postcomp W) ≪≫ (pointedValueMorphismUniversalActionIso f).symm

end SerrePositivity.InfinityCategories.F2
