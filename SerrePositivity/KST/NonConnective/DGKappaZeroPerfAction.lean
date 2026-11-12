module

public import SerrePositivity.KST.NonConnective.DGKappaZeroFunctor
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGLabelAction

/-!
概要：同じ実零 dg 自己関手の、元のラベル付き Perf 上の作用の零対象性。
方針：全入力 Hom に対する実 dg ラベル作用で、同じ閉恒等射の消滅を写す。
規約：全ラベルで同じ零関手を使う。使われ方：全 native Perf 作用の零角。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ) (Z : DGKappaZeroInput R D I)

/-- 同じ零自己関手の実 Perf 作用は、各ラベルで閉零対象を返す。 -/
lemma dgKappaZeroPerfAction_closed_isZero (X : PresentedPerfectDGObject R (DGKappaCone R D I)) :
    IsZero (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R)
      ((presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I)
        (dgKappaZeroFunctor R D I Z)).obj X)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  have h := congrArg
    ((presentedPerfectDGLabelAction R (DGKappaCone R D I) (DGKappaCone R D I) X).onClosed.map)
    ((dgKappaZeroFunctor_isZero R D I Z).eq_of_src
      (𝟙 (ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex R) (dgKappaZeroFunctor R D I Z))) 0)
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at h
  exact h

/-- 同じ実 Perf 作用の各出力は、元の native nerve で始対象かつ終対象。 -/
lemma dgKappaZeroPerfAction_isZeroVertex (X : PresentedPerfectDGObject R (DGKappaCone R D I)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (PresentedPerfectDGObject R (DGKappaCone R D I)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex
        ((presentedPerfectDGAction R (DGKappaCone R D I) (DGKappaCone R D I)
          (dgKappaZeroFunctor R D I Z)).obj X)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isZeroVertex_of_closed_isZero _ (dgKappaZeroPerfAction_closed_isZero R D I Z X)

end SerrePositivity.KST.NonConnective
