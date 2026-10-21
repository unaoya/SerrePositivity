module

public import SerrePositivity.InfinityCategories.F1.CocartesianTransportCutPureHom
public import SerrePositivity.InfinityCategories.F1.CoherentHomConstantTransport

/-!
概要：薄い底の上の同時刻 Hom を、指定された同じ底対象へ正規化する。
方針：計算済みの定値 Hom を対象の等号に沿って移し、薄い底の射の一意性を使う。
規約：対象や輸送射の新しい選択は行わない。
使われ方：第一三角形の同時刻の四つのラベル対の Hom の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同時刻零の Hom を指定底対象へ揃えると、同じ二対象間の元の輸送射になる。 -/
lemma cocartesianTransportHomCutSimplex_zeroHom_at
    {C : Type u} [Category.{u} C] [Quiver.IsThin C]
    (F G : CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : t i = 0) (hj : t j = 0) {c d : C}
    (hc : σ.obj i = c) (hd : σ.obj j = d) (f : c ⟶ d) :
    (cocartesianTransportHomCutSimplex F G σ s t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          ((cocartesianTransportHomCutSimplex_obj_zero F G σ s t i hi).trans
            (congrArg (cocartesianTransportDiagramValue F) hc))
          ((cocartesianTransportHomCutSimplex_obj_zero F G σ s t j hj).trans
            (congrArg (cocartesianTransportDiagramValue F) hd))) =
      SSet.const (SimplicialCategory.homEquiv' (cocartesianTransportDiagramValue F c)
        (cocartesianTransportDiagramValue F d) (F.val.map f)) := by
  exact simplicialHom_constant_transport _
    (cocartesianTransportHomCutSimplex_obj_zero F G σ s t i hi)
    (cocartesianTransportHomCutSimplex_obj_zero F G σ s t j hj) _
    (cocartesianTransportHomCutSimplex_zeroHom F G σ s t i j hij hi hj)
    (congrArg (cocartesianTransportDiagramValue F) hc)
    (congrArg (cocartesianTransportDiagramValue F) hd) _
    (functor_map_transport_of_isThin (cocartesianTransportDiagramValueFunctor F)
      hc hd (σ.map (homOfLE hij)) f)

/-- 同時刻一の Hom を指定底対象へ揃えると、同じ二対象間の元の輸送射になる。 -/
lemma cocartesianTransportHomCutSimplex_oneHom_at
    {C : Type u} [Category.{u} C] [Quiver.IsThin C]
    (F G : CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (s : (SimplicialCategory.sHom F G) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hij : i ≤ j)
    (hi : t i = 1) (hj : t j = 1) {c d : C}
    (hc : σ.obj i = c) (hd : σ.obj j = d) (f : c ⟶ d) :
    (cocartesianTransportHomCutSimplex F G σ s t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          ((cocartesianTransportHomCutSimplex_obj_one F G σ s t i hi).trans
            (congrArg (cocartesianTransportDiagramValue G) hc))
          ((cocartesianTransportHomCutSimplex_obj_one F G σ s t j hj).trans
            (congrArg (cocartesianTransportDiagramValue G) hd))) =
      SSet.const (SimplicialCategory.homEquiv' (cocartesianTransportDiagramValue G c)
        (cocartesianTransportDiagramValue G d) (G.val.map f)) := by
  exact simplicialHom_constant_transport _
    (cocartesianTransportHomCutSimplex_obj_one F G σ s t i hi)
    (cocartesianTransportHomCutSimplex_obj_one F G σ s t j hj) _
    (cocartesianTransportHomCutSimplex_oneHom F G σ s t i j hij hi hj)
    (congrArg (cocartesianTransportDiagramValue G) hc)
    (congrArg (cocartesianTransportDiagramValue G) hd) _
    (functor_map_transport_of_isThin (cocartesianTransportDiagramValueFunctor G)
      hc hd (σ.map (homOfLE hij)) f)

end SerrePositivity.InfinityCategories
