module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.DGComparisons.DGRestrictionGradedComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGYonedaClosedRightShift

/-! # 像の斉次元から制限代表への全 Hom 元を作る

概要：像の Hom の斉次元を、元の代表から制限代表への斉次 Hom へ戻す。
方針：制限代表の Yoneda 鎖同型の逆と微分との可換性を使う。
規約：像の元は任意の整数次数。使われ方：商の全次数の分数表示の入力。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 像の斉次元を制限代表への全 Hom 元に持ち上げる。 -/
def dgRestrictionGradedLift {x y : D} (n : ℤ)
    (c : GradedHom A (F.obj x) (F.obj y) n) :
    (moduleHom A D (representable A x)
      (restrictModule A D E F.op (representable A (F.obj y)))).X n :=
  (dgYonedaIso A x (restrictModule A D E F.op (representable A (F.obj y)))).inv.f n c

omit [Small.{u} E] in
/-- 持ち上げた元を評価すると、元の像の元に厳密に戻る。 -/
lemma dgRestrictionGradedLift_evaluation {x y : D} (n : ℤ)
    (c : GradedHom A (F.obj x) (F.obj y) n) :
    (dgYonedaIso A x (restrictModule A D E F.op (representable A (F.obj y)))).hom.f n
      (dgRestrictionGradedLift A D E F n c) = c := by
  unfold dgRestrictionGradedLift
  have h := congrArg (fun f => f.f n c)
    (dgYonedaIso A x (restrictModule A D E F.op (representable A (F.obj y)))).inv_hom_id
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    ModuleCat.comp_apply, ModuleCat.id_apply] using h

omit [Small.{u} E] in
/-- 持ち上げは像の斉次閉元を実際の全 Hom の閉元に送る。 -/
lemma dgRestrictionGradedLift_closed {x y : D} (n : ℤ)
    (c : GradedHom A (F.obj x) (F.obj y) n) (hc : differential A c = 0) :
    (moduleHom A D (representable A x)
      (restrictModule A D E F.op (representable A (F.obj y)))).d n (n + 1)
        (dgRestrictionGradedLift A D E F n c) = 0 := by
  have h := ConcreteCategory.congr_hom
    ((dgYonedaIso A x (restrictModule A D E F.op (representable A (F.obj y)))).inv.comm
      n (n + 1)) c
  change (moduleHom A D (representable A x)
    (restrictModule A D E F.op (representable A (F.obj y)))).d n (n + 1)
      (dgRestrictionGradedLift A D E F n c) =
        (dgYonedaIso A x (restrictModule A D E F.op (representable A (F.obj y)))).inv.f
          (n + 1) (differential A c) at h
  exact h.trans ((congrArg
    ((dgYonedaIso A x (restrictModule A D E F.op (representable A (F.obj y)))).inv.f (n + 1))
    hc).trans (map_zero _))

/-- 像の斉次閉元から作る、制限代表の shift への実閉加群射。 -/
def dgRestrictionGradedLiftClosed {x y : D} (n : ℤ)
    (c : GradedHom A (F.obj x) (F.obj y) n) (hc : differential A c = 0) :
    ForgetEnrichment.of (Complex A) (representable A x) ⟶
      ((moduleRestriction A D E F.op).obj
        (ForgetEnrichment.of (Complex A) (representable A (F.obj y))))⟦n⟧ :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleClosedRightShift A D n (dgRestrictionGradedLift A D E F n c)
    (dgRestrictionGradedLift_closed A D E F n c hc)

end SerrePositivity.InfinityCategories.Project.DerivedCategories
