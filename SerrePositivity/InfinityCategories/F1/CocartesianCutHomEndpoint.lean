module

public import SerrePositivity.InfinityCategories.F1.CocartesianSourceCutMixedHom

/-!
概要：元の切断した混合 Hom の終点を、固定成分と同じ底対象へ正規化する。
方針：底対象の等号を消去して、検証済みの同じ固定成分の作用へ帰着する。
規約：固定成分と元の source の単体は移し替えず、そのまま使う。
使われ方：第一三角形の終点ラベル 2 での固定成分の Hom の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 切断した混合 Hom の終点を、同じ固定成分の底対象へ揃える。 -/
lemma cocartesianTransportHomCutSimplex_fixedMixedHom_at
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) {n : ℕ}
    (σ : (nerve C) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hij : i ≤ j) (hi : t i = 0) (hj : t j = 1)
    {d : C} (hd : σ.obj j = d)
    (b : ((SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom (cocartesianTransportDiagramValue F d)
        (cocartesianTransportDiagramValue G d))) _⦋0⦌)
    (s : (vertexFiber (cocartesianHomSourceComponent F G d) b) _⦋n⦌) :
    (cocartesianTransportHomCutSimplex F G σ s.val.down t).map ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (cocartesianTransportHomCutSimplex_obj_zero F G σ s.val.down t i hi)
          ((cocartesianTransportHomCutSimplex_obj_one F G σ s.val.down t j hj).trans
            (congrArg (cocartesianTransportDiagramValue G) hd))) =
      SSet.const ((quasicategoryCoreMap ((pre (F.val.map
        (σ.map (homOfLE hij) ≫ eqToHom hd))).app (G.val.obj d))).app
          (Opposite.op ⦋0⦌) b.down) := by
  subst d
  simpa only [eqToHom_refl, Category.comp_id] using
    cocartesianTransportHomCutSimplex_fixedMixedHom F G σ t i j hij hi hj b s

end SerrePositivity.InfinityCategories
