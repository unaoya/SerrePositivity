module
public import SerrePositivity.InfinityCategories.Derived.DGFiniteCellGradedPrimitives
public import SerrePositivity.InfinityCategories.Derived.DGGradedClosedPrecomposition

/-! # 代表始域の加群 Hom の閉前合成の微分・恒等・合成

概要：元の閉射の Yoneda 像による前合成を、全次数の微分・閉性・実恒等と合成へ接続する。
方針：全加群 dg 圏の閉前合成と、Yoneda の閉零関手の恒等・合成保存を使う。
規約：標的加群と整数次数は任意。使われ方：有限個の残差を共通始域へ揃える。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.HomotopyComparison
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 代表始域加群 Hom の閉前合成は、全整数次数の実微分と厳密に可換。 -/
lemma dgRepresentableModulePrecompose_d {q x : D} {M : RightModule A D}
    (n k : ℤ) (hnk : n + 1 = k) (f : GradedHom A (representable A x) M n)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    (moduleHom A D (representable A q) M).d n k (dgRepresentableModulePrecompose A D n f s) =
      dgRepresentableModulePrecompose A D k ((moduleHom A D (representable A x) M).d n k f) s :=
  dgGradedPrecompose_d A (RightModule A D) n k hnk f ((dgYoneda A D).onClosed.map s)

/-- 同じ閉前合成は任意次数の斉次閉元を保つ。 -/
lemma dgRepresentableModulePrecompose_closed {q x : D} {M : RightModule A D}
    (n : ℤ) (f : GradedHom A (representable A x) M n) (hf : differential A f = 0)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    differential A (dgRepresentableModulePrecompose A D n f s) = 0 :=
  dgGradedPrecompose_closed A (RightModule A D) n f hf ((dgYoneda A D).onClosed.map s)

/-- 元の恒等閉射による前合成は、全次数で厳密に恒等。 -/
lemma dgRepresentableModulePrecompose_id {x : D} {M : RightModule A D}
    (n : ℤ) (f : GradedHom A (representable A x) M n) :
    dgRepresentableModulePrecompose A D n f (𝟙 (ForgetEnrichment.of (Complex A) x)) = f := by
  have hi : (closedHomEquiv A (RightModule A D) _ _
      ((dgYoneda A D).onClosed.map (𝟙 (ForgetEnrichment.of (Complex A) x)))).val =
      (unitElement A (representable A x)).val :=
    (congrArg (fun g : (dgYoneda A D).onClosed.obj (ForgetEnrichment.of (Complex A) x) ⟶
      (dgYoneda A D).onClosed.obj (ForgetEnrichment.of (Complex A) x) =>
        (closedHomEquiv A (RightModule A D) _ _ g).val)
          ((dgYoneda A D).onClosed.map_id _)).trans
            (congrArg Subtype.val (closedHom_id
              ((dgYoneda A D).onClosed.obj (ForgetEnrichment.of (Complex A) x))))
  exact (congrArg (fun a : GradedHom A (representable A x) (representable A x) 0 =>
    compose A f a (zero_add n)) hi).trans (compose_unit A f)

/-- 元の閉射の指定合成による前合成は、二段の実前合成と厳密に一致。 -/
lemma dgRepresentableModulePrecompose_comp {p q x : D} {M : RightModule A D}
    (n : ℤ) (f : GradedHom A (representable A x) M n)
    (r : ForgetEnrichment.of (Complex A) p ⟶ ForgetEnrichment.of (Complex A) q)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    dgRepresentableModulePrecompose A D n (dgRepresentableModulePrecompose A D n f s) r =
      dgRepresentableModulePrecompose A D n f (r ≫ s) := by
  have hc := dgGradedPrecompose_comp A (RightModule A D) n f
    ((dgYoneda A D).onClosed.map r) ((dgYoneda A D).onClosed.map s)
  exact hc.trans (congrArg (fun t : (dgYoneda A D).onClosed.obj
    (ForgetEnrichment.of (Complex A) p) ⟶ (dgYoneda A D).onClosed.obj
      (ForgetEnrichment.of (Complex A) x) => dgGradedPrecompose A (RightModule A D) n f t)
        ((dgYoneda A D).onClosed.map_comp r s).symm)

end SerrePositivity.InfinityCategories
