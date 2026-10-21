module
public import SerrePositivity.InfinityCategories.DGNerve.FunctorMapping
/-!
概要：任意の dg 関手は、同じ斉次 shift の閉射と両単位との差の境界関係を保つ。
方針：実入力射影の全射準同型性と、同じ Hom 複体の微分・合成の保存を使う。
規約：全高次 Hom の検査を省かない。使われ方：一般 Morita 不変性の shift 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (C : Type v) (E : Type w) [DGCategory R C] [DGCategory R E]
/-- 同じ全次数の斉次射と両単位関係の実原始元の構成。 -/
lemma dgFunctor_gradedShiftHomotopyInverse {x y : C} (G : DGFunctor R C E) (s : ℤ)
    (f : GradedHom R x y (-s)) (g : GradedHom R y x s)
    (hf : differential R f = 0) (hg : differential R g = 0)
    (hX : GradedHom R x x (-1))
    (hhX : (homObject R C x x).d (-1) 0 hX =
      compose R g f (neg_add_cancel s) - (unitElement R x).val)
    (hY : GradedHom R y y (-1))
    (hhY : (homObject R C y y).d (-1) 0 hY =
      compose R f g (add_neg_cancel s) - (unitElement R y).val) :
    differential R ((G.map x y).f (-s) f) = 0 ∧
      differential R ((G.map y x).f s g) = 0 ∧
    ∃ hGX : GradedHom R (G.obj x) (G.obj x) (-1),
      (homObject R E (G.obj x) (G.obj x)).d (-1) 0 hGX =
        compose R ((G.map y x).f s g) ((G.map x y).f (-s) f) (neg_add_cancel s) -
          (unitElement R (G.obj x)).val ∧
    ∃ hGY : GradedHom R (G.obj y) (G.obj y) (-1),
      (homObject R E (G.obj y) (G.obj y)).d (-1) 0 hGY =
        compose R ((G.map x y).f (-s) f) ((G.map y x).f s g) (add_neg_cancel s) -
          (unitElement R (G.obj y)).val := by
  refine ⟨?_, ?_, (G.map x x).f (-1) hX, ?_, (G.map y y).f (-1) hY, ?_⟩
  · rw [← map_differential G, hf, map_zero]
  · rw [← map_differential G, hg, map_zero]
  · calc
      _ = (G.map x x).f 0 ((homObject R C x x).d (-1) 0 hX) :=
        ConcreteCategory.congr_hom ((G.map x x).comm (-1) 0) hX
      _ = _ := by rw [hhX, map_sub, DGNerve.map_compose, G.map_unitElement R]
  · calc
      _ = (G.map y y).f 0 ((homObject R C y y).d (-1) 0 hY) :=
        ConcreteCategory.congr_hom ((G.map y y).comm (-1) 0) hY
      _ = _ := by rw [hhY, map_sub, DGNerve.map_compose, G.map_unitElement R]

end SerrePositivity.InfinityCategories
