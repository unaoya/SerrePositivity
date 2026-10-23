module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.FirstTriangleSourceMaps
public import SerrePositivity.InfinityCategories.F1.CoherentOrderHomNormalization
public import SerrePositivity.InfinityCategories.F1.Cocartesian.CutMixedHomEndpoint

/-!
概要：元の第一三角形の混合 Hom を、指定三角形の同じ合成射に同定する。
方針：同じ二対象への正規化で、固定成分を前合成した射と指定射列の射を比較する。
規約：元の source の成分 fiber を全次数で保持する。
使われ方：第一三角形全体の豊穣関手の等式の混合の場合。
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

/-- 元の第一三角形の終点へ向かう全 Hom は、指定三角形の同じ Hom。 -/
lemma cocartesianFirstTriangleCutSimplex_mixedHom_eq {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌)
    (s : (vertexFiber (cocartesianHomSourceComponent F G (ULift.up 1)) b) _⦋n⦌)
    (i j : Fin (n + 1)) (hij : i ≤ j) (k : Fin 2)
    (hi : (stdSimplex.objEquiv a) i = k.castSucc) (hj : (stdSimplex.objEquiv a) j = 2) :
    (cocartesianFirstTriangleCutSimplex F G a s.val.down).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (cocartesianFirstTriangleCutSimplex_obj F G b a s.val.down i)
          (cocartesianFirstTriangleCutSimplex_obj F G b a s.val.down j)) =
      (cocartesianFirstTriangleCanonicalSimplex F G b a).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ := by
  let f := homOfLE (show (ULift.up k : ULift.{u} (Fin 2)) ≤ ULift.up 1 from Fin.le_last _)
  let D := cocartesianFirstTriangleSourceOrderDiagram F G b
  let α := (stdSimplex.objEquiv a).toOrderHom.uliftMap
  let g := homOfLE (show (ULift.up k.castSucc : ULift.{u} (Fin 3)) ≤ ULift.up 2
    from Fin.le_last _)
  let k₁ := (SimplicialCategory.homEquiv' (cocartesianTransportDiagramValue F (ULift.up 1))
    (cocartesianTransportDiagramValue G (ULift.up 1))).symm b.down
  have hR₀ := orderDiagramEnrichedHom_reindex_normalized α D
    ⟨ULift.up i⟩ ⟨ULift.up j⟩ hij (congrArg ULift.up hi) (congrArg ULift.up hj) g
  have hR := simplicialHom_constant_transport _
    (congrArg D.obj (congrArg ULift.up hi)) (congrArg D.obj (congrArg ULift.up hj)) _ hR₀
    (cocartesianFirstTriangleSourceOrderDiagram_obj_zero F G b k) rfl
    ((cocartesianTransportDiagramValueFunctor F).map f ≫ k₁) (by
      erw [Category.comp_id]
      exact cocartesianFirstTriangleSourceOrderDiagram_map_to_last F G b k)
  have hL := cocartesianTransportHomCutSimplex_fixedMixedHom_normalized F G
    (cocartesianFirstTriangleBaseSimplex a) (cocartesianFirstTriangleTime a) i j hij
    (cocartesianFirstTriangleTime_zero a i k hi) (cocartesianFirstTriangleTime_one a j hj)
    (cocartesianFirstTriangleBaseSimplex_obj_zero a i k hi)
    (cocartesianFirstTriangleBaseSimplex_obj_one a j hj) f b s
  exact simplicialHom_eq_of_normalized _ _
    (cocartesianFirstTriangleCutSimplex_obj F G b a s.val.down i)
    (cocartesianFirstTriangleCutSimplex_obj F G b a s.val.down j)
    ((cocartesianTransportHomCutSimplex_obj_zero F G _ s.val.down _ i
      (cocartesianFirstTriangleTime_zero a i k hi)).trans
        (congrArg (cocartesianTransportDiagramValue F)
          (cocartesianFirstTriangleBaseSimplex_obj_zero a i k hi)))
    ((cocartesianTransportHomCutSimplex_obj_one F G _ s.val.down _ j
      (cocartesianFirstTriangleTime_one a j hj)).trans
        (congrArg (cocartesianTransportDiagramValue G)
          (cocartesianFirstTriangleBaseSimplex_obj_one a j hj)))
    (cocartesianFirstTriangleCanonicalSimplex_obj_zero F G b a i k hi)
    (cocartesianFirstTriangleCanonicalSimplex_obj_one F G b a j hj) (hL.trans hR.symm)

end SerrePositivity.InfinityCategories
