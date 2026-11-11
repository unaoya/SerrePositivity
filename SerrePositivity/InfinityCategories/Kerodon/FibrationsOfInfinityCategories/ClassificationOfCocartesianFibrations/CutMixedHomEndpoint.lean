module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CutHomEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomConstantTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.MixedHomVertices

/-!
概要：固定成分に向かう混合 Hom を、指定された通常の合成射へ正規化する。
方針：元の core の前合成頂点を通常の射として読み、薄い底の射の移送を計算する。
規約：元の source の成分 fiber と、同じ混合 Hom 作用を保持する。
使われ方：第一三角形のラベル 0,2 と 1,2 の Hom を指定合成と同定する。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 指定底対象へ正規化した元の混合 Hom は、同じ輸送射と固定成分の通常の合成。 -/
lemma cocartesianTransportHomCutSimplex_fixedMixedHom_normalized
    {C : Type u} [Category.{u} C] [Quiver.IsThin C]
    (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hij : i ≤ j) (hi : t i = 0) (hj : t j = 1)
    {c d : C} (hc : σ.obj i = c) (hd : σ.obj j = d) (f : c ⟶ d)
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F d)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G d))) _⦋0⦌)
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomSourceComponent F G d) b) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex F G σ s.val.down t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_obj_zero F G σ s.val.down t i hi).trans
            (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F) hc))
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_obj_one F G σ s.val.down t j hj).trans
            (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G) hd))) =
      SSet.const (SimplicialCategory.homEquiv' (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F c)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G d) (F.val.map f ≫
          (SimplicialCategory.homEquiv' (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F d)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G d)).symm b.down)) := by
  let k := (SimplicialCategory.homEquiv' (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F d)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G d)).symm b.down
  have hk : SimplicialCategory.homEquiv' _ _ k = b.down := Equiv.apply_symm_apply _ _
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_fixedMixedHom_at F G σ t i j hij hi hj hd b s
  rw [← hk] at h
  erw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.qCatHomVertex_pre (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F (σ.obj i))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F d) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G d)
    (F.val.map (σ.map (homOfLE hij) ≫ eqToHom hd)) k] at h
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_constant_transport _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_obj_zero F G σ s.val.down t i hi)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportHomCutSimplex_obj_one F G σ s.val.down t j hj).trans
      (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G) hd)) _ h
    (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F) hc) rfl _ ?_
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.functor_map_transport_of_isThin (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValueFunctor F)
    hc rfl (σ.map (homOfLE hij) ≫ eqToHom hd) f
  change eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F) hc).symm ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValueFunctor F).map (σ.map (homOfLE hij) ≫ eqToHom hd) ≫
      𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F d) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValueFunctor F).map f at hm
  change (eqToHom (congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F) hc).symm ≫
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValueFunctor F).map
      (σ.map (homOfLE hij) ≫ eqToHom hd) ≫ k)) ≫ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G d) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValueFunctor F).map f ≫ k
  erw [Category.comp_id] at hm
  erw [Category.comp_id, ← Category.assoc, hm]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
