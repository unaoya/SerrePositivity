module
public import SerrePositivity.InfinityCategories.Derived.DGSemifreeGradedShift
/-!
概要：元の shift の斉次閉射と両単位の境界原始元を、実分解 dg 圏へ持ち上げる。
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
variable (R : Type u) [CommRing R]
/-- 同じ全次数の斉次射と両単位関係の実原始元の構成。 -/
lemma dgModuleResolution_gradedShiftHomotopyInverse
    (B : Type v) [DGCategory R B] [Small.{u} B]
    (E : Type w) [DGCategory R E] [Small.{u} E]
    (F : DGFunctor R (SemifreeDGModules R B) (RightModule R E))
    (X : DGModuleFunctorResolutionObject R (SemifreeDGModules R B) E F) (s : ℤ) :
    ∃ (Y : DGModuleFunctorResolutionObject R (SemifreeDGModules R B) E F)
      (f : GradedHom R X Y (-s)) (g : GradedHom R Y X s),
      differential R f = 0 ∧ differential R g = 0 ∧
      ∃ hX : GradedHom R X X (-1),
        (homObject R _ X X).d (-1) 0 hX =
          compose R g f (neg_add_cancel s) - (unitElement R X).val ∧
      ∃ hY : GradedHom R Y Y (-1),
        (homObject R _ Y Y).d (-1) 0 hY =
          compose R f g (add_neg_cancel s) - (unitElement R Y).val := by
  obtain ⟨N, f0, g0, hf0, hg0, hM, hhM, hN, hhN⟩ :=
    dgSemifreeShift_gradedHomotopyInverse R B X.source s
  obtain ⟨Y, hY⟩ := dgModuleFunctorResolutionSource_obj_surjective R (SemifreeDGModules R B) E F N
  change Y.source = N at hY
  subst N
  obtain ⟨f, hf, hPf⟩ := dgModuleResolutionSource_closed_lift R (SemifreeDGModules R B) E F
    X Y (-s) f0 hf0
  obtain ⟨g, hg, hPg⟩ := dgModuleResolutionSource_closed_lift R (SemifreeDGModules R B) E F
    Y X s g0 hg0
  let P := dgModuleFunctorResolutionSource R (SemifreeDGModules R B) E F
  let aX : GradedHom R X X 0 := compose R g f (neg_add_cancel s) - (unitElement R X).val
  let aY : GradedHom R Y Y 0 := compose R f g (add_neg_cancel s) - (unitElement R Y).val
  have haX : differential R aX = 0 := by
    dsimp only [aX]
    simp only [differential_sub, differential_compose, hg, hf, zero_compose, compose_zero,
      smul_zero, zero_add, differential_unit, sub_zero]
  have haY : differential R aY = 0 := by
    dsimp only [aY]
    simp only [differential_sub, differential_compose, hf, hg, zero_compose, compose_zero,
      smul_zero, zero_add, differential_unit, sub_zero]
  have hbX : differential R (D := SemifreeDGModules R B)
      (x := X.source) (y := X.source) hM = (P.map X X).f 0 aX := by
    dsimp only [aX]
    rw [map_sub, DGNerve.map_compose, P.map_unitElement R, hPf, hPg]
    exact hhM
  have hbY : differential R (D := SemifreeDGModules R B)
      (x := Y.source) (y := Y.source) hN = (P.map Y Y).f 0 aY := by
    dsimp only [aY]
    rw [map_sub, DGNerve.map_compose, P.map_unitElement R, hPf, hPg]
    exact hhN
  have hrX := dgModuleResolutionSource_boundary_reflect R (SemifreeDGModules R B) E F X X (-1)
  have hrY := dgModuleResolutionSource_boundary_reflect R (SemifreeDGModules R B) E F Y Y (-1)
  obtain ⟨hX, hhX⟩ := hrX aX haX hM hbX
  obtain ⟨hY, hhY⟩ := hrY aY haY hN hbY
  exact ⟨Y, f, g, hf, hg, hX, hhX, hY, hhY⟩

end SerrePositivity.InfinityCategories
