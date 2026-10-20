module
public import SerrePositivity.KST.SConstruction.DGTensorFunctor
public import SerrePositivity.KST.SConstruction.DGTensorAssociator
public import SerrePositivity.KST.SConstruction.DGTensorBraiding
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGTensorAction
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInputHomHorizontal

/-! # 同じ三重 tensor 始域を持つ二つの元の Perf 作用
概要：右入力・左入力・ラベルの同じ順の三重 tensor から、二回作用と合成入力作用を作る。
方針：元の結合・signed 交換・tensor dg 関手で始域を揃える。
規約：全 Hom の非離散な作用を保持する。使われ方：二回の高次入力作用の関手等号。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T]

/-- 右入力・左入力・元のラベルの三重 tensor 上の、元の二回の dg 作用。 -/
def presentedPerfectDGTensorIterated :
    DGFunctor A (DGTensorCategory A
      (DGTensorCategory A (DGFunctor A E T) (DGFunctor A D E)) (PresentedPerfectDGObject A D))
      (PresentedPerfectDGObject A T) :=
  (dgTensorAssociator A (DGFunctor A E T) (DGFunctor A D E) (PresentedPerfectDGObject A D)).comp
    ((dgTensorFunctor A (DGFunctor.id (DGFunctor A E T))
      (presentedPerfectDGTensorAction A D E)).comp
      (presentedPerfectDGTensorAction A E T))

/-- 同じ三重 tensor 上で、元の入力横合成を先に作用させる dg 関手。 -/
def presentedPerfectDGTensorComposite :
    DGFunctor A (DGTensorCategory A
      (DGTensorCategory A (DGFunctor A E T) (DGFunctor A D E)) (PresentedPerfectDGObject A D))
      (PresentedPerfectDGObject A T) :=
  (dgTensorFunctor A
    ((dgTensorBraiding A (DGFunctor A E T) (DGFunctor A D E)).comp
      (dgFunctorHorizontalDG A D E T)) (DGFunctor.id (PresentedPerfectDGObject A D))).comp
        (presentedPerfectDGTensorAction A D T)

/-- 二回作用と合成入力作用の対象比較は、既存の同じラベル合成等号。 -/
lemma presentedPerfectDGTensorIterated_obj
    (x : DGTensorCategory A
      (DGTensorCategory A (DGFunctor A E T) (DGFunctor A D E)) (PresentedPerfectDGObject A D)) :
    (presentedPerfectDGTensorIterated A D E T).obj x =
      (presentedPerfectDGTensorComposite A D E T).obj x :=
  presentedPerfectDGActionObject_comp A D E T x.1.2 x.1.1 x.2

/-- 二回作用の全 Hom は、元の結合と二つの tensor 作用の同じ合成。 -/
lemma presentedPerfectDGTensorIterated_map
    (x y : DGTensorCategory A
      (DGTensorCategory A (DGFunctor A E T) (DGFunctor A D E)) (PresentedPerfectDGObject A D)) :
    (presentedPerfectDGTensorIterated A D E T).map x y =
      (α_ (dgFunctorHom A E T x.1.1 y.1.1) (dgFunctorHom A D E x.1.2 y.1.2)
          (homObject A (PresentedPerfectDGObject A D) x.2 y.2)).hom ≫
        (𝟙 (dgFunctorHom A E T x.1.1 y.1.1) ⊗ₘ
          presentedPerfectDGTensorHom A D E x.1.2 y.1.2 x.2 y.2) ≫
          presentedPerfectDGTensorHom A E T x.1.1 y.1.1
            ((presentedPerfectDGAction A D E x.1.2).obj x.2)
            ((presentedPerfectDGAction A D E y.1.2).obj y.2) := by
  simp only [presentedPerfectDGTensorIterated, DGFunctor.comp, EnrichedFunctor.comp_map,
    dgTensorAssociator_map, dgTensorFunctor_map, presentedPerfectDGTensorAction_map,
    DGFunctor.id, EnrichedFunctor.id_map]
  dsimp only [dgTensorAssociator, dgTensorFunctor, EnrichedFunctor.id,
    presentedPerfectDGTensorAction]
  rfl

/-- 合成入力作用の全 Hom は、元の signed 交換・横合成・tensor 作用の同じ合成。 -/
lemma presentedPerfectDGTensorComposite_map
    (x y : DGTensorCategory A
      (DGTensorCategory A (DGFunctor A E T) (DGFunctor A D E)) (PresentedPerfectDGObject A D)) :
    (presentedPerfectDGTensorComposite A D E T).map x y =
      ((dgTensorBraidingHom A (DGFunctor A E T) (DGFunctor A D E) x.1 y.1 ≫
          dgFunctorHorizontal A D E T x.1.2 y.1.2 x.1.1 y.1.1) ⊗ₘ
        𝟙 (homObject A (PresentedPerfectDGObject A D) x.2 y.2)) ≫
          presentedPerfectDGTensorHom A D T (x.1.2.comp x.1.1) (y.1.2.comp y.1.1) x.2 y.2 := by
  simp only [presentedPerfectDGTensorComposite, DGFunctor.comp, EnrichedFunctor.comp_map,
    dgTensorFunctor_map, dgTensorBraiding_map, presentedPerfectDGTensorAction_map,
    DGFunctor.id, EnrichedFunctor.id_map]
  rfl

end SerrePositivity.KST.SConstruction
