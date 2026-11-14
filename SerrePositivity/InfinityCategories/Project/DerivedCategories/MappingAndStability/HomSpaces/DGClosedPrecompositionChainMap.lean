module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.HomSpaces.DGGradedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.DGModules.Actions.DGModuleHomPrecompose
public import SerrePositivity.DifferentialGraded.Module.Graded

/-! # 元の閉射による Hom 鎖写像

概要：元の dg Hom 複体の前合成を、全 Hom Yoneda 鎖同型の共役として構成する。
方針：加群 Hom の閉射による前合成の成分を、元の斉次合成へ厳密に戻す。
規約：対象と全整数次数を固定する。使われ方：実 pinched Hom の分母による前合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]

/-- 全 Hom Yoneda によって構成した、元の閉射による前合成鎖写像。 -/
def dgClosedPrecomposition {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ homObject A D q y :=
  _root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y ≫ eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex A) ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s)
    (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A y) : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D) ≫
      (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso A q (_root_.SerrePositivity.DifferentialGraded.representable A y)).hom

/-- 前合成鎖写像の全次数成分は、元の斉次前合成と厳密に一致する。 -/
lemma dgClosedPrecomposition_f {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x)
    (k : ℤ) (a : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k) :
    (dgClosedPrecomposition A D (y := y) s).f k a = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k a s := by
  change (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso A q (_root_.SerrePositivity.DifferentialGraded.representable A y)).hom.f k
    ((eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex A) ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A y) : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D)).f k
        ((_root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y).f k a)) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleHom_precompose_eq_compose]
  have hs := congrArg Subtype.val ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).closedHomEquiv_map s)
  change (_root_.SerrePositivity.DifferentialGraded.cycleFromUnit _ (ForgetEnrichment.homTo (_root_.SerrePositivity.DifferentialGraded.Complex A)
    ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s))).val =
      (_root_.SerrePositivity.DifferentialGraded.yonedaHom A D q x).f 0 (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val at hs
  rw [hs]
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.map_compose (dgYoneda A D) (x := q) (y := x) (z := y)
    a (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val (zero_add k)
  change (yonedaHom A D q y).f k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k a s) =
    _root_.SerrePositivity.DifferentialGraded.compose A (D := _root_.SerrePositivity.DifferentialGraded.RightModule A D) (x := _root_.SerrePositivity.DifferentialGraded.representable A q) (y := _root_.SerrePositivity.DifferentialGraded.representable A x)
      (z := _root_.SerrePositivity.DifferentialGraded.representable A y) ((_root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y).f k a)
      ((_root_.SerrePositivity.DifferentialGraded.yonedaHom A D q x).f 0 (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val) (zero_add k) at hm
  rw [← hm]
  have hi := congrArg (fun f => f.f k (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose A D k a s))
    (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso A q (_root_.SerrePositivity.DifferentialGraded.representable A y)).inv_hom_id
  simpa only [_root_.SerrePositivity.DifferentialGraded.yonedaHom, HomologicalComplex.comp_f, HomologicalComplex.id_f,
    ModuleCat.comp_apply, ModuleCat.id_apply] using hi

/-- 閉分母の二回の前合成は、指定された閉射の合成による前合成と一致する。 -/
lemma dgClosedPrecomposition_comp {p q x y : D}
    (r : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) p ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    dgClosedPrecomposition A D (y := y) s ≫ dgClosedPrecomposition A D (y := y) r =
      dgClosedPrecomposition A D (y := y) (r ≫ s) := by
  apply HomologicalComplex.Hom.ext
  funext k
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (dgClosedPrecomposition A D (y := y) r).f k
    ((dgClosedPrecomposition A D (y := y) s).f k a) = _
  rw [dgClosedPrecomposition_f, dgClosedPrecomposition_f, dgClosedPrecomposition_f,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgGradedPrecompose_comp]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
