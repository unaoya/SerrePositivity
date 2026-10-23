module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.FirstTriangleObjects
public import SerrePositivity.InfinityCategories.F1.CoherentOrderHomNormalization
public import SerrePositivity.InfinityCategories.F1.Cocartesian.CutPureHomEndpoint

/-!
概要：元の第一三角形の最終ラベルの Hom を、指定三角形の恒等射に同定する。
方針：元の終域図式の恒等射保存と、同じ二対象への正規化を使う。
規約：元の全高次 Hom の作用を保持する。
使われ方：第一三角形全体の豊穣関手の等式の同時刻一の場合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

variable (F G : CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
variable (b : ((SSet.uliftFunctor.{u + 1, u}).obj
  (SimplicialCategory.sHom (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1)))) _⦋0⦌)

/-- 元の第一三角形の最終ラベルの全 Hom は、指定三角形の同じ Hom。 -/
lemma cocartesianFirstTriangleCutSimplex_oneHom_eq {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : (stdSimplex.objEquiv a) i = 2) (hj : (stdSimplex.objEquiv a) j = 2) :
    (cocartesianFirstTriangleCutSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (cocartesianFirstTriangleCutSimplex_obj F G b a s i)
          (cocartesianFirstTriangleCutSimplex_obj F G b a s j)) =
      (cocartesianFirstTriangleCanonicalSimplex F G b a).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ := by
  let D := cocartesianFirstTriangleSourceOrderDiagram F G b
  let α := (stdSimplex.objEquiv a).toOrderHom.uliftMap
  have hR := orderDiagramEnrichedHom_reindex_normalized α D
    ⟨ULift.up i⟩ ⟨ULift.up j⟩ hij (congrArg ULift.up hi) (congrArg ULift.up hj)
    (𝟙 (ULift.up (2 : Fin 3)))
  rw [D.map_id] at hR
  have hL := cocartesianTransportHomCutSimplex_oneHom_at F G
    (cocartesianFirstTriangleBaseSimplex a) s (cocartesianFirstTriangleTime a) i j hij
    (cocartesianFirstTriangleTime_one a i hi) (cocartesianFirstTriangleTime_one a j hj)
    (cocartesianFirstTriangleBaseSimplex_obj_one a i hi)
    (cocartesianFirstTriangleBaseSimplex_obj_one a j hj) (𝟙 (ULift.up (1 : Fin 2)))
  rw [G.val.map_id] at hL
  exact simplicialHom_eq_of_normalized _ _
    (cocartesianFirstTriangleCutSimplex_obj F G b a s i)
    (cocartesianFirstTriangleCutSimplex_obj F G b a s j)
    ((cocartesianTransportHomCutSimplex_obj_one F G _ s _ i
      (cocartesianFirstTriangleTime_one a i hi)).trans
        (congrArg (cocartesianTransportDiagramValue G)
          (cocartesianFirstTriangleBaseSimplex_obj_one a i hi)))
    ((cocartesianTransportHomCutSimplex_obj_one F G _ s _ j
      (cocartesianFirstTriangleTime_one a j hj)).trans
        (congrArg (cocartesianTransportDiagramValue G)
          (cocartesianFirstTriangleBaseSimplex_obj_one a j hj)))
    (cocartesianFirstTriangleCanonicalSimplex_obj_one F G b a i hi)
    (cocartesianFirstTriangleCanonicalSimplex_obj_one F G b a j hj) (hL.trans hR.symm)

end SerrePositivity.InfinityCategories
