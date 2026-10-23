module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.CutHomEndpoint
public import SerrePositivity.InfinityCategories.F1.CoherentHomConstantTransport
public import SerrePositivity.InfinityCategories.F1.Cocartesian.MixedHomVertices

/-!
概要：固定成分に向かう混合 Hom を、指定された通常の合成射へ正規化する。
方針：元の core の前合成頂点を通常の射として読み、薄い底の射の移送を計算する。
規約：元の source の成分 fiber と、同じ混合 Hom 作用を保持する。
使われ方：第一三角形のラベル 0,2 と 1,2 の Hom を指定合成と同定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 指定底対象へ正規化した元の混合 Hom は、同じ輸送射と固定成分の通常の合成。 -/
lemma cocartesianTransportHomCutSimplex_fixedMixedHom_normalized
    {C : Type u} [Category.{u} C] [Quiver.IsThin C]
    (F G : CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hij : i ≤ j) (hi : t i = 0) (hj : t j = 1)
    {c d : C} (hc : σ.obj i = c) (hd : σ.obj j = d) (f : c ⟶ d)
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (cocartesianTransportDiagramValue F d)
        (cocartesianTransportDiagramValue G d))) _⦋0⦌)
    (s : (vertexFiber (cocartesianHomSourceComponent F G d) b) _⦋n⦌) :
    (cocartesianTransportHomCutSimplex F G σ s.val.down t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          ((cocartesianTransportHomCutSimplex_obj_zero F G σ s.val.down t i hi).trans
            (congrArg (cocartesianTransportDiagramValue F) hc))
          ((cocartesianTransportHomCutSimplex_obj_one F G σ s.val.down t j hj).trans
            (congrArg (cocartesianTransportDiagramValue G) hd))) =
      SSet.const (SimplicialCategory.homEquiv' (cocartesianTransportDiagramValue F c)
        (cocartesianTransportDiagramValue G d) (F.val.map f ≫
          (SimplicialCategory.homEquiv' (cocartesianTransportDiagramValue F d)
            (cocartesianTransportDiagramValue G d)).symm b.down)) := by
  let k := (SimplicialCategory.homEquiv' (cocartesianTransportDiagramValue F d)
    (cocartesianTransportDiagramValue G d)).symm b.down
  have hk : SimplicialCategory.homEquiv' _ _ k = b.down := Equiv.apply_symm_apply _ _
  have h := cocartesianTransportHomCutSimplex_fixedMixedHom_at F G σ t i j hij hi hj hd b s
  rw [← hk] at h
  erw [qCatHomVertex_pre (cocartesianTransportDiagramValue F (σ.obj i))
    (cocartesianTransportDiagramValue F d) (cocartesianTransportDiagramValue G d)
    (F.val.map (σ.map (homOfLE hij) ≫ eqToHom hd)) k] at h
  refine simplicialHom_constant_transport _
    (cocartesianTransportHomCutSimplex_obj_zero F G σ s.val.down t i hi)
    ((cocartesianTransportHomCutSimplex_obj_one F G σ s.val.down t j hj).trans
      (congrArg (cocartesianTransportDiagramValue G) hd)) _ h
    (congrArg (cocartesianTransportDiagramValue F) hc) rfl _ ?_
  have hm := functor_map_transport_of_isThin (cocartesianTransportDiagramValueFunctor F)
    hc rfl (σ.map (homOfLE hij) ≫ eqToHom hd) f
  change eqToHom (congrArg (cocartesianTransportDiagramValue F) hc).symm ≫
    (cocartesianTransportDiagramValueFunctor F).map (σ.map (homOfLE hij) ≫ eqToHom hd) ≫
      𝟙 (cocartesianTransportDiagramValue F d) =
        (cocartesianTransportDiagramValueFunctor F).map f at hm
  change (eqToHom (congrArg (cocartesianTransportDiagramValue F) hc).symm ≫
    ((cocartesianTransportDiagramValueFunctor F).map
      (σ.map (homOfLE hij) ≫ eqToHom hd) ≫ k)) ≫ 𝟙 (cocartesianTransportDiagramValue G d) =
      (cocartesianTransportDiagramValueFunctor F).map f ≫ k
  erw [Category.comp_id] at hm
  erw [Category.comp_id, ← Category.assoc, hm]

end SerrePositivity.InfinityCategories
