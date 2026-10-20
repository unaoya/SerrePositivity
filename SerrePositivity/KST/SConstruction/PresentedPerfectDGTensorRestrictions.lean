module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGTensorAction
public import SerrePositivity.DifferentialGraded.Category.TensorInclusions

/-! # tensor dg 作用から元の二つの作用の厳密な回収
概要：片方の対象を固定して閉単位を挿入すると、元の入力作用・ラベル作用へ戻る。
方針：純斉次成分で元の単位挿入を評価し、各 dg 関手の単位保存と単位則を使う。
規約：全次数 Hom の等号として比較する。使われ方：高次作用と既存作用との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- ラベルの閉単位を挿入した tensor Hom 作用は、元の入力 Hom 作用そのもの。 -/
lemma presentedPerfectDGTensorHom_first (X : PresentedPerfectDGObject A D)
    (F G : DGFunctor A D E) :
    dgTensorFirstHom A (DGFunctor A D E) (PresentedPerfectDGObject A D) X F G ≫
        presentedPerfectDGTensorHom A D E F G X X = presentedPerfectDGInputHom A D E F G X := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  ext a
  change (presentedPerfectDGTensorHom A D E F G X X).f n
      ((dgTensorFirstHom A (DGFunctor A D E) (PresentedPerfectDGObject A D) X F G).f n a) = _
  rw [dgTensorFirstHom_apply]
  have hm := presentedPerfectDGTensorHom_apply A D E a (unitElement A X).val (add_zero n)
  have hu := DGFunctor.map_unitElement A (presentedPerfectDGAction A D E G) X
  exact hm.trans ((congrArg (fun z =>
    forward A ((presentedPerfectDGInputHom A D E F G X).f n a) z (add_zero n)) hu).trans
      (unit_forward A _))

/-- 入力の閉単位を挿入した tensor Hom 作用は、元のラベル Hom 作用そのもの。 -/
lemma presentedPerfectDGTensorHom_second (F : DGFunctor A D E)
    (X Y : PresentedPerfectDGObject A D) :
    dgTensorSecondHom A (DGFunctor A D E) (PresentedPerfectDGObject A D) F X Y ≫
        presentedPerfectDGTensorHom A D E F F X Y = (presentedPerfectDGAction A D E F).map X Y := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  ext b
  change (presentedPerfectDGTensorHom A D E F F X Y).f n
      ((dgTensorSecondHom A (DGFunctor A D E) (PresentedPerfectDGObject A D) F X Y).f n b) = _
  rw [dgTensorSecondHom_apply]
  have hm := presentedPerfectDGTensorHom_apply A D E (unitElement A F).val b (zero_add n)
  have hu := DGFunctor.map_unitElement A (presentedPerfectDGLabelAction A D E X) F
  simp only [presentedPerfectDGLabelAction_map] at hu
  exact hm.trans ((congrArg (fun z =>
    forward A z (((presentedPerfectDGAction A D E F).map X Y).f n b) (zero_add n)) hu).trans
      (forward_unit A _))

/-- ラベルを固定した tensor dg 作用は、元の固定ラベルの dg 関手と厳密に一致する。 -/
lemma presentedPerfectDGTensorAction_first (X : PresentedPerfectDGObject A D) :
    (dgTensorIncludeFirst A (DGFunctor A D E) (PresentedPerfectDGObject A D) X).comp
        (presentedPerfectDGTensorAction A D E) = presentedPerfectDGLabelAction A D E X := by
  refine EnrichedFunctor.ext (Complex A)
    (F := (dgTensorIncludeFirst A (DGFunctor A D E) (PresentedPerfectDGObject A D) X).comp
      (presentedPerfectDGTensorAction A D E))
    (G := presentedPerfectDGLabelAction A D E X) (fun _ => rfl) ?_
  intro F G
  change (_ ≫ presentedPerfectDGTensorHom A D E F G X X) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact presentedPerfectDGTensorHom_first A D E X F G

/-- 入力を固定した tensor dg 作用は、元の同じラベル上の dg 関手と厳密に一致する。 -/
lemma presentedPerfectDGTensorAction_second (F : DGFunctor A D E) :
    (dgTensorIncludeSecond A (DGFunctor A D E) (PresentedPerfectDGObject A D) F).comp
        (presentedPerfectDGTensorAction A D E) = presentedPerfectDGAction A D E F := by
  refine EnrichedFunctor.ext (Complex A)
    (F := (dgTensorIncludeSecond A (DGFunctor A D E) (PresentedPerfectDGObject A D) F).comp
      (presentedPerfectDGTensorAction A D E))
    (G := presentedPerfectDGAction A D E F) (fun _ => rfl) ?_
  intro X Y
  change (_ ≫ presentedPerfectDGTensorHom A D E F F X Y) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact presentedPerfectDGTensorHom_second A D E F X Y

end SerrePositivity.KST.SConstruction
