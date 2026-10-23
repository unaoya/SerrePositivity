module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.FirstTriangleSourceMaps
public import SerrePositivity.InfinityCategories.F1.Coherent.OrderHomNormalization
public import SerrePositivity.InfinityCategories.F1.Cocartesian.CutPureHomEndpoint

/-!
概要：元の第一三角形の時刻零の Hom を、指定三角形の同じ Hom に同定する。
方針：両側を同じ二つの底対象へ正規化し、元の輸送射の等式で比較する。
規約：任意次数の元の Hom パラメーターを保持する。
使われ方：第一三角形全体の豊穣関手の等式の同時刻零の場合。
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

/-- 元の第一三角形の最初の二ラベルの全 Hom は、指定三角形の同じ Hom。 -/
lemma cocartesianFirstTriangleCutSimplex_zeroHom_eq {n : ℕ}
    (a : (Δ[2] : SSet.{u + 1}) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (i j : Fin (n + 1)) (hij : i ≤ j) (k l : Fin 2)
    (hi : (stdSimplex.objEquiv a) i = k.castSucc)
    (hj : (stdSimplex.objEquiv a) j = l.castSucc) :
    (cocartesianFirstTriangleCutSimplex F G a s).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (cocartesianFirstTriangleCutSimplex_obj F G b a s i)
          (cocartesianFirstTriangleCutSimplex_obj F G b a s j)) =
      (cocartesianFirstTriangleCanonicalSimplex F G b a).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ := by
  have hkl : k ≤ l := Fin.castSucc_le_castSucc_iff.mp (by
    rw [← hi, ← hj]; exact (stdSimplex.objEquiv a).toOrderHom.monotone hij)
  let f := homOfLE (show (ULift.up k : ULift.{u} (Fin 2)) ≤ ULift.up l from hkl)
  let D := cocartesianFirstTriangleSourceOrderDiagram F G b
  let α := (stdSimplex.objEquiv a).toOrderHom.uliftMap
  let g := homOfLE (show (ULift.up k.castSucc : ULift.{u} (Fin 3)) ≤ ULift.up l.castSucc
    from Fin.castSucc_le_castSucc_iff.mpr hkl)
  have hR₀ := orderDiagramEnrichedHom_reindex_normalized α D
    ⟨ULift.up i⟩ ⟨ULift.up j⟩ hij (congrArg ULift.up hi) (congrArg ULift.up hj) g
  have hR := simplicialHom_constant_transport _
    (congrArg D.obj (congrArg ULift.up hi)) (congrArg D.obj (congrArg ULift.up hj)) _ hR₀
    (cocartesianFirstTriangleSourceOrderDiagram_obj_zero F G b k)
    (cocartesianFirstTriangleSourceOrderDiagram_obj_zero F G b l)
    ((cocartesianTransportDiagramValueFunctor F).map f)
    (cocartesianFirstTriangleSourceOrderDiagram_map_zero F G b k l hkl)
  have hL := cocartesianTransportHomCutSimplex_zeroHom_at F G
    (cocartesianFirstTriangleBaseSimplex a) s (cocartesianFirstTriangleTime a) i j hij
    (cocartesianFirstTriangleTime_zero a i k hi) (cocartesianFirstTriangleTime_zero a j l hj)
    (cocartesianFirstTriangleBaseSimplex_obj_zero a i k hi)
    (cocartesianFirstTriangleBaseSimplex_obj_zero a j l hj) f
  exact simplicialHom_eq_of_normalized _ _
    (cocartesianFirstTriangleCutSimplex_obj F G b a s i)
    (cocartesianFirstTriangleCutSimplex_obj F G b a s j)
    ((cocartesianTransportHomCutSimplex_obj_zero F G _ s _ i
      (cocartesianFirstTriangleTime_zero a i k hi)).trans
        (congrArg (cocartesianTransportDiagramValue F)
          (cocartesianFirstTriangleBaseSimplex_obj_zero a i k hi)))
    ((cocartesianTransportHomCutSimplex_obj_zero F G _ s _ j
      (cocartesianFirstTriangleTime_zero a j l hj)).trans
        (congrArg (cocartesianTransportDiagramValue F)
          (cocartesianFirstTriangleBaseSimplex_obj_zero a j l hj)))
    (cocartesianFirstTriangleCanonicalSimplex_obj_zero F G b a i k hi)
    (cocartesianFirstTriangleCanonicalSimplex_obj_zero F G b a j l hj) (hL.trans hR.symm)

end SerrePositivity.InfinityCategories
