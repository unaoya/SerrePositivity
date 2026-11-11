module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeGradedShift
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R]
/-- 同じ全次数の斉次射と両単位関係の実原始元の構成。 -/
lemma dgModuleResolution_gradedShiftHomotopyInverse
    (B : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R B] [Small.{u} B]
    (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
    (F : DGFunctor R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B) (RightModule R E))
    (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B) E F) (s : ℤ) :
    ∃ (Y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B) E F)
      (f : _root_.SerrePositivity.DifferentialGraded.GradedHom R X Y (-s)) (g : _root_.SerrePositivity.DifferentialGraded.GradedHom R Y X s),
      _root_.SerrePositivity.DifferentialGraded.differential R f = 0 ∧ _root_.SerrePositivity.DifferentialGraded.differential R g = 0 ∧
      ∃ hX : _root_.SerrePositivity.DifferentialGraded.GradedHom R X X (-1),
        (_root_.SerrePositivity.DifferentialGraded.homObject R _ X X).d (-1) 0 hX =
          _root_.SerrePositivity.DifferentialGraded.compose R g f (neg_add_cancel s) - (_root_.SerrePositivity.DifferentialGraded.unitElement R X).val ∧
      ∃ hY : _root_.SerrePositivity.DifferentialGraded.GradedHom R Y Y (-1),
        (_root_.SerrePositivity.DifferentialGraded.homObject R _ Y Y).d (-1) 0 hY =
          _root_.SerrePositivity.DifferentialGraded.compose R f g (add_neg_cancel s) - (_root_.SerrePositivity.DifferentialGraded.unitElement R Y).val := by
  obtain ⟨N, f0, g0, hf0, hg0, hM, hhM, hN, hhN⟩ :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeShift_gradedHomotopyInverse R B X.source s
  obtain ⟨Y, hY⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource_obj_surjective R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B) E F N
  change Y.source = N at hY
  subst N
  obtain ⟨f, hf, hPf⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionSource_closed_lift R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B) E F
    X Y (-s) f0 hf0
  obtain ⟨g, hg, hPg⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionSource_closed_lift R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B) E F
    Y X s g0 hg0
  let P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B) E F
  let aX : GradedHom R X X 0 := _root_.SerrePositivity.DifferentialGraded.compose R g f (neg_add_cancel s) - (_root_.SerrePositivity.DifferentialGraded.unitElement R X).val
  let aY : GradedHom R Y Y 0 := _root_.SerrePositivity.DifferentialGraded.compose R f g (add_neg_cancel s) - (_root_.SerrePositivity.DifferentialGraded.unitElement R Y).val
  have haX : _root_.SerrePositivity.DifferentialGraded.differential R aX = 0 := by
    dsimp only [aX]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_sub, differential_compose, hg, hf, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero,
      smul_zero, zero_add, _root_.SerrePositivity.DifferentialGraded.differential_unit, sub_zero]
  have haY : _root_.SerrePositivity.DifferentialGraded.differential R aY = 0 := by
    dsimp only [aY]
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_sub, differential_compose, hf, hg, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.zero_compose, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.compose_zero,
      smul_zero, zero_add, _root_.SerrePositivity.DifferentialGraded.differential_unit, sub_zero]
  have hbX : differential R (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B)
      (x := X.source) (y := X.source) hM = (P.map X X).f 0 aX := by
    dsimp only [aX]
    rw [map_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose, P.map_unitElement R, hPf, hPg]
    exact hhM
  have hbY : differential R (D := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B)
      (x := Y.source) (y := Y.source) hN = (P.map Y Y).f 0 aY := by
    dsimp only [aY]
    rw [map_sub, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose, P.map_unitElement R, hPf, hPg]
    exact hhN
  have hrX := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionSource_boundary_reflect R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B) E F X X (-1)
  have hrY := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionSource_boundary_reflect R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R B) E F Y Y (-1)
  obtain ⟨hX, hhX⟩ := hrX aX haX hM hbX
  obtain ⟨hY, hhY⟩ := hrY aY haY hN hbY
  exact ⟨Y, f, g, hf, hg, hX, hhX, hY, hhY⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
