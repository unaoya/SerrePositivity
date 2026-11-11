module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedPrecompositionChainMap
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGClosedHomWhiskerNaturality

/-! # 閉射による元の全 Hom 複体の後合成

概要：指定閉零射による全 Hom 鎖後合成を作り、全 Hom Yoneda の共役等式を証明する。
方針：豊穣前後合成の自然性を Yoneda の Hom 同型で消去する。
規約：全整数次数を保持する。使われ方：有限パラメータの実 Ore 細分の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 指定閉零射による、元の全 Hom 複体の豊穣後合成。 -/
def dgClosedPostcomposition {x y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) :
    _root_.SerrePositivity.DifferentialGraded.homObject A D x y ⟶ homObject A D x z :=
  eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex A) (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) s

variable [Small.{u} D]

/-- 元の全 Hom 後合成は、全 Hom Yoneda 同型による加群 Hom 後合成の共役。 -/
lemma dgClosedPostcomposition_yonedaConjugate {x y z : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) z) :
    dgClosedPostcomposition A D (x := x) s =
      _root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y ≫ eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex A)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A x) : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D)
          ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s) ≫ (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso A x (_root_.SerrePositivity.DifferentialGraded.representable A z)).hom := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorHom_postcompose (dgYoneda A D) (ForgetEnrichment.of (Complex A) x) s
  change dgClosedPostcomposition A D (x := x) s ≫ _root_.SerrePositivity.DifferentialGraded.yonedaHom A D x z =
    _root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y ≫ eHomWhiskerLeft (_root_.SerrePositivity.DifferentialGraded.Complex A)
      (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A x) : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D)
      ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s) at h
  have ht := congrArg (fun k => k ≫ (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso A x (_root_.SerrePositivity.DifferentialGraded.representable A z)).hom) h
  simpa only [dgClosedPostcomposition, _root_.SerrePositivity.DifferentialGraded.yonedaHom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using ht

/-- 既存の全 Hom 前合成は、元の閉射の標準豊穣前合成と厳密に一致する。 -/
lemma dgClosedPrecomposition_eq_whisker {q x y : D}
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition A D (y := y) s =
      eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex A) s (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorHom_precompose (dgYoneda A D) s (ForgetEnrichment.of (Complex A) y)
  change eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex A) s (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) y) ≫
    _root_.SerrePositivity.DifferentialGraded.yonedaHom A D q y = _root_.SerrePositivity.DifferentialGraded.yonedaHom A D x y ≫
      eHomWhiskerRight (_root_.SerrePositivity.DifferentialGraded.Complex A) ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s)
        (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) (_root_.SerrePositivity.DifferentialGraded.representable A y) : _root_.SerrePositivity.DifferentialGraded.ModuleCategory A D) at h
  have ht := congrArg (fun k => k ≫ (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso A q (_root_.SerrePositivity.DifferentialGraded.representable A y)).hom) h
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgClosedPrecomposition, yonedaHom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using ht.symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
