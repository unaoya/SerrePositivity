module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGYonedaGradedPrimitives
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import SerrePositivity.DifferentialGraded.Module.FreeSphere

/-! # 制限代表比較の全次数 Yoneda 評価

概要：元の斉次射の Yoneda 像を制限比較で後合成し評価すると、元の dg 関手の像になる。
方針：Yoneda の後合成の鎖写像の自然性と、比較の objectwise の公式を使う。
規約：平坦性不要。使われ方：商で境界であることを実 Hom end の原始元へ戻す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 制限代表比較の全 Hom 鎖写像を Yoneda で評価すると、元の dg Hom 写像。 -/
lemma dgRestrictionGradedComparison_evaluation (x y : D) :
    yonedaHom A D x y ≫ eHomWhiskerLeft (Complex A)
      (ForgetEnrichment.of (Complex A) (representable A x) : ModuleCategory A D)
      (representableRestrictionMap A D E F y) ≫
        (dgYonedaIso A x (restrictModule A D E F.op (representable A (F.obj y)))).hom =
      F.map x y := by
  have hn := dgYonedaIso_postcompose A D x (representableRestrictionMap A D E F y)
  have he := congrArg (fun g => yonedaHom A D x y ≫ g) hn
  calc
    _ = yonedaHom A D x y ≫ (dgYonedaIso A x (representable A y)).hom ≫
        (moduleEvaluation A D x).map (representableRestrictionMap A D E F y) := he
    _ = F.map x y := by
      rw [yonedaHom, Iso.inv_hom_id_assoc, representableRestrictionMap_eval]

/-- 元の dg Hom の像の境界性から、制限比較後の全 Hom end の原始元を回収する。 -/
lemma dgRestrictionGradedComparison_exists_primitive {x y : D} (k n : ℤ)
    (a : GradedHom A x y n)
    (ha : ∃ b : GradedHom A (F.obj x) (F.obj y) k,
      (homObject A E (F.obj x) (F.obj y)).d k n b = (F.map x y).f n a) :
    ∃ b : (moduleHom A D (representable A x)
      (restrictModule A D E F.op (representable A (F.obj y)))).X k,
      (moduleHom A D (representable A x)
        (restrictModule A D E F.op (representable A (F.obj y)))).d k n b =
          (eHomWhiskerLeft (Complex A)
            (ForgetEnrichment.of (Complex A) (representable A x) : ModuleCategory A D)
            (representableRestrictionMap A D E F y)).f n ((yonedaHom A D x y).f n a) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgComplexIso_exists_primitive_iff A
    (dgYonedaIso A x (restrictModule A D E F.op (representable A (F.obj y)))).hom k n _).mp
  have he := congrArg (fun f => f.f n a) (dgRestrictionGradedComparison_evaluation A D E F x y)
  change (dgYonedaIso A x (restrictModule A D E F.op (representable A (F.obj y)))).hom.f n
    ((eHomWhiskerLeft (Complex A)
      (ForgetEnrichment.of (Complex A) (representable A x) : ModuleCategory A D)
      (representableRestrictionMap A D E F y)).f n ((yonedaHom A D x y).f n a)) =
        (F.map x y).f n a at he
  rw [he]
  exact ha

end SerrePositivity.InfinityCategories.Project.DerivedCategories
