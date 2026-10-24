module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentTriangleLastTailHead
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ReflectedCoefficientPostcomposition
/-!
概要：最大化側の最後辺の実 head を、元の第一射の係数作用に続く最後射へ揃える。
方針：同じ初点固定 tail の二時刻の式に、反転係数の後合成則と豊穣結合則を適用する。
規約：元の全次数の係数を保持する。
使われ方：Ncomp の実 prism の全 head の一致。
-/

@[expose] public section
noncomputable section
open CategoryTheory SSet SimplicialThickening MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (s : SpaceInfinity.{u} _⦋2⦌)
/-- 概要：零時刻の head は元の第一射による全係数の後合成。
方針：同じ tail の定値 Hom を計算する。
規約：元の全係数を保持。使われ方：最後辺の実 head の照合。 -/
lemma coherentTriangleLastInitialHead_zero {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (p : (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op _⦋n⦌)
    (j : Fin (n + 1)) (hj : α.toOrderHom j = 0) :
    coneInitialHead pointKanObject (coherentTriangleLastTail s α).val
      (SSet.yonedaEquiv.symm p) j ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom rfl
        (coherentTriangleLastTail_obj_zero s α j hj)) =
      pathFirstParameterMap j ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm p) ≫
        eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s)) := by
  rw [coneInitialHead_transport_target pointKanObject
    (coherentTriangleLastTail s α).val (SSet.yonedaEquiv.symm p) j
    (coherentTriangleLastTail_obj_zero s α j hj),
    coherentTriangleLastTail_head_zero s α j hj]
  convert simplicialHom_head_postcomp
    (pathFirstParameterMap j ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm p))
    (coherentEdgeHom (SpaceInfinity.δ 2 s)) using 1 <;> rfl
/-- 概要：一時刻の head は第一射を作用させた同じ全係数と最後射の合成。
方針：同じ tail の定値 Hom を計算する。
規約：元の全係数を保持。使われ方：最後辺の実 head の照合。 -/
lemma coherentTriangleLastInitialHead_one {n : ℕ} (α : ⦋n⦌ ⟶ ⦋1⦌)
    (p : (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op _⦋n⦌)
    (j : Fin (n + 1)) (hj : α.toOrderHom j = 1) :
    coneInitialHead pointKanObject (coherentTriangleLastTail s α).val
      (SSet.yonedaEquiv.symm p) j ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom rfl
        (coherentTriangleLastTail_obj_one s α j hj)) =
      lift (pathFirstParameterMap j ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm p) ≫
        eHomWhiskerLeft SSet pointKanObject (coherentEdgeHom (SpaceInfinity.δ 2 s)))
        (SSet.const (SimplicialCategory.homEquiv' _ _ (coherentEdgeHom (SpaceInfinity.δ 0 s)))) ≫
        eComp SSet pointKanObject (s.obj ⟨ULift.up 1⟩) (s.obj ⟨ULift.up 2⟩) := by
  rw [coneInitialHead_transport_target pointKanObject
    (coherentTriangleLastTail s α).val (SSet.yonedaEquiv.symm p) j
    (coherentTriangleLastTail_obj_one s α j hj),
    coherentTriangleLastTail_head_one s α j hj]
  convert (simplicialHom_postcomp_head
    (pathFirstParameterMap j ≫ reflectedSimplexMap (SSet.yonedaEquiv.symm p))
    (coherentEdgeHom (SpaceInfinity.δ 2 s))
    (coherentEdgeHom (SpaceInfinity.δ 0 s))).symm using 1 <;> rfl
end SerrePositivity.InfinityCategories.F2
