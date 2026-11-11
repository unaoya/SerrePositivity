module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleYonedaPrecomposition
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFiniteCellGradedPrimitives

/-! # 任意の代表始域 Hom 元の閉前合成と Yoneda 評価

概要：追加閉分母の Yoneda 像による前合成を、元の加群作用へ厳密に戻す。
方針：Yoneda の両逆性で既存の逆写像の評価公式を任意の Hom 元へ拡張する。
規約：任意の標的・整数次数。使われ方：実残差の同じ閉細分による二座標。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex CochainComplex HomComplex Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
/-- 代表加群の次数零作用は、元の通常順の前合成そのもの。 -/
lemma dgRepresentableZeroAction (x q y : D) (n : ℤ) (s : GradedHom A q x 0)
    (f : GradedHom A x y n) :
    moduleAction A (representable A y) (x := op x) (y := op q) s f (add_zero n) =
      compose A f s (zero_add n) := by
  change forward A s f (zero_add n) = compose A f s (zero_add n)
  simp only [compose, Int.zero_mul, Int.negOnePow_zero, one_smul]

/-- 閉前合成された任意の代表始域 Hom 元の Yoneda 評価は、元の加群作用。 -/
lemma dgRepresentableModulePrecompose_evaluation (x q : D) (M : RightModule A D) (n : ℤ)
    (f : GradedHom A (representable A x) M n)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    (dgYonedaIso A q M).hom.f n (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableModulePrecompose A D n f s) =
      moduleAction A M (x := op x) (y := op q) (closedHomEquiv A D _ _ s).val
        ((dgYonedaIso A x M).hom.f n f) (add_zero n) := by
  have hi : (dgYonedaIso A x M).inv.f n ((dgYonedaIso A x M).hom.f n f) = f :=
    congrArg (fun a => a.f n f) (dgYonedaIso A x M).hom_inv_id
  have he := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaInverse_precompose_evaluation A D x q M n
    ((dgYonedaIso A x M).hom.f n f) (closedHomEquiv A D _ _ s).val
  rw [hi] at he
  have hg : (closedHomEquiv A (RightModule A D) _ _ ((dgYoneda A D).onClosed.map s)).val =
      (yonedaHom A D q x).f 0 (closedHomEquiv A D _ _ s).val :=
    congrArg Subtype.val ((dgYoneda A D).closedHomEquiv_map s)
  change (dgYonedaIso A q M).hom.f n
    (compose A f (closedHomEquiv A (RightModule A D) _ _
      ((dgYoneda A D).onClosed.map s)).val (zero_add n)) = _
  rw [hg]
  exact he

end SerrePositivity.InfinityCategories.Project.DerivedCategories
