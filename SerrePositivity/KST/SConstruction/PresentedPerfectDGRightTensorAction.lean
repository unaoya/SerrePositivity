module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGTensorRestrictions
public import SerrePositivity.KST.SConstruction.DGTensorBraiding

/-! # ラベルを先に置く Perf の実 dg 右作用
概要：ラベル Hom と入力関手 Hom の順で、元の全次数 tensor 作用を与える。
方針：元の signed braiding の後に元のラベル付き Perf tensor 作用を適用する。
規約：Koszul 符号と非対称な Serre 対角の因子順を保持。使われ方：native 右作用。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [DGCategory A E] [Small.{u} D] [Small.{u} E]

/-- ラベル・関手の順から、元の signed braiding を通して実 Perf 作用を行う。 -/
def presentedPerfectDGRightTensorAction :
    DGFunctor A (DGTensorCategory A (PresentedPerfectDGObject A D) (DGFunctor A D E))
      (PresentedPerfectDGObject A E) :=
  DGFunctor.comp
    (dgTensorBraiding A (PresentedPerfectDGObject A D) (DGFunctor A D E))
    (presentedPerfectDGTensorAction A D E)

/-- 実右作用の対象は、元の同じ厳密 dg 入力のラベル作用を回収する。 -/
lemma presentedPerfectDGRightTensorAction_obj
    (x : DGTensorCategory A (PresentedPerfectDGObject A D) (DGFunctor A D E)) :
    (presentedPerfectDGRightTensorAction A D E).obj x =
      (presentedPerfectDGAction A D E x.2).obj x.1 := rfl

/-- 実右作用の全 Hom は、元の signed 交換と元の全次数 Perf tensor 作用。 -/
lemma presentedPerfectDGRightTensorAction_map
    (x y : DGTensorCategory A (PresentedPerfectDGObject A D) (DGFunctor A D E)) :
    (presentedPerfectDGRightTensorAction A D E).map x y =
      dgTensorBraidingHom A (PresentedPerfectDGObject A D) (DGFunctor A D E) x y ≫
        presentedPerfectDGTensorHom A D E x.2 y.2 x.1 y.1 := rfl

/-- 元の入力関手を固定した実右作用は、全 Hom 上で元のラベル作用を回収する。 -/
lemma presentedPerfectDGRightTensorAction_fixed (F : DGFunctor A D E) :
    DGFunctor.comp
        (dgTensorIncludeFirst A (PresentedPerfectDGObject A D) (DGFunctor A D E) F)
        (presentedPerfectDGRightTensorAction A D E) = presentedPerfectDGAction A D E F := by
  refine EnrichedFunctor.ext (Complex A) (fun _ => rfl) ?_
  intro X Y
  apply (Category.comp_id _).trans
  change dgTensorFirstHom A (PresentedPerfectDGObject A D) (DGFunctor A D E) F X Y ≫
    (dgTensorBraidingHom A (PresentedPerfectDGObject A D) (DGFunctor A D E) (X, F) (Y, F) ≫
      presentedPerfectDGTensorHom A D E F F X Y) = _
  rw [← Category.assoc]
  exact presentedPerfectDGTensorHom_second A D E F X Y

/-- ラベルを先に置く全 Hom 作用は、元の signed 交換と元の tensor 作用。 -/
def presentedPerfectDGRightTensorHom (F G : DGFunctor A D E)
    (X Y : PresentedPerfectDGObject A D) :
    homObject A (PresentedPerfectDGObject A D) X Y ⊗ dgFunctorHom A D E F G ⟶
      homObject A (PresentedPerfectDGObject A E)
        ((presentedPerfectDGAction A D E F).obj X) ((presentedPerfectDGAction A D E G).obj Y) :=
  (β_ (homObject A (PresentedPerfectDGObject A D) X Y) (dgFunctorHom A D E F G)).hom ≫
    presentedPerfectDGTensorHom A D E F G X Y

/-- 実 dg 右作用の各 Hom は、同じラベル先行の全次数 Hom 作用。 -/
lemma presentedPerfectDGRightTensorAction_hom
    (x y : DGTensorCategory A (PresentedPerfectDGObject A D) (DGFunctor A D E)) :
    (presentedPerfectDGRightTensorAction A D E).map x y =
      presentedPerfectDGRightTensorHom A D E x.2 y.2 x.1 y.1 := rfl

end SerrePositivity.KST.SConstruction
