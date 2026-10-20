module
public import SerrePositivity.InfinityCategories.Derived.DGClosedPrecompositionChainMap
public import SerrePositivity.InfinityCategories.Derived.DGClosedHomWhiskerNaturality

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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 指定閉零射による、元の全 Hom 複体の豊穣後合成。 -/
def dgClosedPostcomposition {x y z : D}
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z) :
    homObject A D x y ⟶ homObject A D x z :=
  eHomWhiskerLeft (Complex A) (ForgetEnrichment.of (Complex A) x) s

variable [Small.{u} D]

/-- 元の全 Hom 後合成は、全 Hom Yoneda 同型による加群 Hom 後合成の共役。 -/
lemma dgClosedPostcomposition_yonedaConjugate {x y z : D}
    (s : ForgetEnrichment.of (Complex A) y ⟶ ForgetEnrichment.of (Complex A) z) :
    dgClosedPostcomposition A D (x := x) s =
      yonedaHom A D x y ≫ eHomWhiskerLeft (Complex A)
        (ForgetEnrichment.of (Complex A) (representable A x) : ModuleCategory A D)
          ((dgYoneda A D).onClosed.map s) ≫ (dgYonedaIso A x (representable A z)).hom := by
  have h := dgFunctorHom_postcompose (dgYoneda A D) (ForgetEnrichment.of (Complex A) x) s
  change dgClosedPostcomposition A D (x := x) s ≫ yonedaHom A D x z =
    yonedaHom A D x y ≫ eHomWhiskerLeft (Complex A)
      (ForgetEnrichment.of (Complex A) (representable A x) : ModuleCategory A D)
      ((dgYoneda A D).onClosed.map s) at h
  have ht := congrArg (fun k => k ≫ (dgYonedaIso A x (representable A z)).hom) h
  simpa only [dgClosedPostcomposition, yonedaHom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using ht

/-- 既存の全 Hom 前合成は、元の閉射の標準豊穣前合成と厳密に一致する。 -/
lemma dgClosedPrecomposition_eq_whisker {q x y : D}
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    dgClosedPrecomposition A D (y := y) s =
      eHomWhiskerRight (Complex A) s (ForgetEnrichment.of (Complex A) y) := by
  have h := dgFunctorHom_precompose (dgYoneda A D) s (ForgetEnrichment.of (Complex A) y)
  change eHomWhiskerRight (Complex A) s (ForgetEnrichment.of (Complex A) y) ≫
    yonedaHom A D q y = yonedaHom A D x y ≫
      eHomWhiskerRight (Complex A) ((dgYoneda A D).onClosed.map s)
        (ForgetEnrichment.of (Complex A) (representable A y) : ModuleCategory A D) at h
  have ht := congrArg (fun k => k ≫ (dgYonedaIso A q (representable A y)).hom) h
  simpa only [dgClosedPrecomposition, yonedaHom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id] using ht.symm

end SerrePositivity.InfinityCategories
