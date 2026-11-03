module
public import SerrePositivity.InfinityCategories.Derived.DGGradedClosedPrecomposition
public import SerrePositivity.InfinityCategories.Derived.DGModuleHomPrecompose
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 全 Hom Yoneda によって構成した、元の閉射による前合成鎖写像。 -/
def dgClosedPrecomposition {q x y : D}
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    homObject A D x y ⟶ homObject A D q y :=
  yonedaHom A D x y ≫ eHomWhiskerRight (Complex A) ((dgYoneda A D).onClosed.map s)
    (ForgetEnrichment.of (Complex A) (representable A y) : ModuleCategory A D) ≫
      (dgYonedaIso A q (representable A y)).hom

/-- 前合成鎖写像の全次数成分は、元の斉次前合成と厳密に一致する。 -/
lemma dgClosedPrecomposition_f {q x y : D}
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x)
    (k : ℤ) (a : GradedHom A x y k) :
    (dgClosedPrecomposition A D (y := y) s).f k a = dgGradedPrecompose A D k a s := by
  change (dgYonedaIso A q (representable A y)).hom.f k
    ((eHomWhiskerRight (Complex A) ((dgYoneda A D).onClosed.map s)
      (ForgetEnrichment.of (Complex A) (representable A y) : ModuleCategory A D)).f k
        ((yonedaHom A D x y).f k a)) = _
  rw [dgModuleHom_precompose_eq_compose]
  have hs := congrArg Subtype.val ((dgYoneda A D).closedHomEquiv_map s)
  change (cycleFromUnit _ (ForgetEnrichment.homTo (Complex A)
    ((dgYoneda A D).onClosed.map s))).val =
      (yonedaHom A D q x).f 0 (closedHomEquiv A D _ _ s).val at hs
  rw [hs]
  have hm := map_compose (dgYoneda A D) (x := q) (y := x) (z := y)
    a (closedHomEquiv A D _ _ s).val (zero_add k)
  change (yonedaHom A D q y).f k (dgGradedPrecompose A D k a s) =
    compose A (D := RightModule A D) (x := representable A q) (y := representable A x)
      (z := representable A y) ((yonedaHom A D x y).f k a)
      ((yonedaHom A D q x).f 0 (closedHomEquiv A D _ _ s).val) (zero_add k) at hm
  rw [← hm]
  have hi := congrArg (fun f => f.f k (dgGradedPrecompose A D k a s))
    (dgYonedaIso A q (representable A y)).inv_hom_id
  simpa only [yonedaHom, HomologicalComplex.comp_f, HomologicalComplex.id_f,
    ModuleCat.comp_apply, ModuleCat.id_apply] using hi

/-- 閉分母の二回の前合成は、指定された閉射の合成による前合成と一致する。 -/
lemma dgClosedPrecomposition_comp {p q x y : D}
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
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
    dgGradedPrecompose_comp]

end SerrePositivity.InfinityCategories
