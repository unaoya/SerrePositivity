module
public import SerrePositivity.KST.SConstruction.DGTensorAssociatorPostMap
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGRightTensorIteration
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGTensorActionComposition

/-! # 実 Perf 右作用の合成を同じ dg 関手へ束ねる
概要：ラベル先行の三重 tensor 上の二回作用と、元の入力横合成の作用を比較する。
方針：二経路の対象と全 Hom を固定し、元の同じラベル比較による移送で外延性を使う。
規約：元の全次数と signed 交換を保持。使われ方：native 右作用の全単体的合成則。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [DGCategory A E] [DGCategory A T]
  [Small.{u} D] [Small.{u} E] [Small.{u} T]

/-- 元のラベルに前入力、後入力の順で二回作用する実 dg 関手。 -/
def presentedPerfectDGRightTensorIterated :
    DGFunctor A (DGTensorCategory A
      (DGTensorCategory A (PresentedPerfectDGObject A D) (DGFunctor A D E)) (DGFunctor A E T))
      (PresentedPerfectDGObject A T) :=
  DGFunctor.comp
    (dgTensorFunctor A (presentedPerfectDGRightTensorAction A D E) (DGFunctor.id (DGFunctor A E T)))
    (presentedPerfectDGRightTensorAction A E T)

/-- ラベルと右括弧の入力対に、元の入力横合成を先に作用させる実 dg 関手。 -/
def presentedPerfectDGRightTensorCompositeInner :
    DGFunctor A (DGTensorCategory A (PresentedPerfectDGObject A D)
      (DGTensorCategory A (DGFunctor A D E) (DGFunctor A E T))) (PresentedPerfectDGObject A T) :=
  DGFunctor.comp
    (dgTensorFunctor A (DGFunctor.id (PresentedPerfectDGObject A D))
      (dgFunctorHorizontalDG A D E T))
    (presentedPerfectDGRightTensorAction A D T)

/-- 同じ左括弧の三重 tensor から、元の入力横合成を先に作用させる実 dg 関手。 -/
def presentedPerfectDGRightTensorComposite :
    DGFunctor A (DGTensorCategory A
      (DGTensorCategory A (PresentedPerfectDGObject A D) (DGFunctor A D E)) (DGFunctor A E T))
      (PresentedPerfectDGObject A T) :=
  DGFunctor.comp
    (dgTensorAssociator A (PresentedPerfectDGObject A D) (DGFunctor A D E) (DGFunctor A E T))
    (presentedPerfectDGRightTensorCompositeInner A D E T)

/-- 二回の実右作用の対象比較は、元の同じラベル合成等号。 -/
lemma presentedPerfectDGRightTensorIterated_obj
    (x : DGTensorCategory A
      (DGTensorCategory A (PresentedPerfectDGObject A D) (DGFunctor A D E)) (DGFunctor A E T)) :
    (presentedPerfectDGRightTensorIterated A D E T).obj x =
      (presentedPerfectDGRightTensorComposite A D E T).obj x :=
  presentedPerfectDGTensorIterated_obj A D E T ((x.2, x.1.2), x.1.1)

/-- 元の二回の右作用の全 Hom は、同じ二つの右 Hom 作用の tensor 合成。 -/
lemma presentedPerfectDGRightTensorIterated_map
    (x y : DGTensorCategory A
      (DGTensorCategory A (PresentedPerfectDGObject A D) (DGFunctor A D E)) (DGFunctor A E T)) :
    (presentedPerfectDGRightTensorIterated A D E T).map x y =
      (presentedPerfectDGRightTensorHom A D E x.1.2 y.1.2 x.1.1 y.1.1 ⊗ₘ
        𝟙 (dgFunctorHom A E T x.2 y.2)) ≫
        presentedPerfectDGRightTensorHom A E T x.2 y.2
          ((presentedPerfectDGAction A D E x.1.2).obj x.1.1)
          ((presentedPerfectDGAction A D E y.1.2).obj y.1.1) := rfl

/-- 元の右括弧での合成入力作用は、同じ入力横合成と右作用の Hom。 -/
lemma presentedPerfectDGRightTensorCompositeInner_map
    (x y : DGTensorCategory A (PresentedPerfectDGObject A D)
      (DGTensorCategory A (DGFunctor A D E) (DGFunctor A E T))) :
    (presentedPerfectDGRightTensorCompositeInner A D E T).map x y =
      (𝟙 (homObject A (PresentedPerfectDGObject A D) x.1 y.1) ⊗ₘ
        dgFunctorHorizontal A D E T x.2.1 y.2.1 x.2.2 y.2.2) ≫
        presentedPerfectDGRightTensorHom A D T (x.2.1.comp x.2.2) (y.2.1.comp y.2.2) x.1 y.1 := rfl

/-- 元の三重 tensor からの合成入力作用は、同じ結合射と入力横合成と右作用。 -/
lemma presentedPerfectDGRightTensorComposite_map
    (x y : DGTensorCategory A
      (DGTensorCategory A (PresentedPerfectDGObject A D) (DGFunctor A D E)) (DGFunctor A E T)) :
    (presentedPerfectDGRightTensorComposite A D E T).map x y =
      (α_ (homObject A (PresentedPerfectDGObject A D) x.1.1 y.1.1)
        (homObject A (DGFunctor A D E) x.1.2 y.1.2)
        (homObject A (DGFunctor A E T) x.2 y.2)).hom ≫
        (𝟙 (homObject A (PresentedPerfectDGObject A D) x.1.1 y.1.1) ⊗ₘ
          dgFunctorHorizontal A D E T x.1.2 y.1.2 x.2 y.2) ≫
          presentedPerfectDGRightTensorHom A D T
            (x.1.2.comp x.2) (y.1.2.comp y.2) x.1.1 y.1.1 := by
  have h0 := dgTensorAssociator_post_map A (PresentedPerfectDGObject A D)
    (DGFunctor A D E) (DGFunctor A E T) (presentedPerfectDGRightTensorCompositeInner A D E T) x y
  apply h0.trans
  have h := presentedPerfectDGRightTensorCompositeInner_map A D E T
    (x.1.1, (x.1.2, x.2)) (y.1.1, (y.1.2, y.2))
  exact congrArg (fun f => (α_ (homObject A (PresentedPerfectDGObject A D) x.1.1 y.1.1)
    (homObject A (DGFunctor A D E) x.1.2 y.1.2)
    (homObject A (DGFunctor A E T) x.2 y.2)).hom ≫ f) h

/-- 元の二回右作用の全 Hom は、元の対象等号移送によって合成入力作用に等しい。 -/
lemma presentedPerfectDGRightTensorIterated_map_transport
    (x y : DGTensorCategory A
      (DGTensorCategory A (PresentedPerfectDGObject A D) (DGFunctor A D E)) (DGFunctor A E T)) :
    (presentedPerfectDGRightTensorIterated A D E T).map x y ≫
      enrichedClosedIsoConjugation (Complex A)
        (presentedPerfectDGCompositionTransport A D E T x.1.2 x.2 x.1.1)
        (presentedPerfectDGCompositionTransport A D E T y.1.2 y.2 y.1.1) =
      (presentedPerfectDGRightTensorComposite A D E T).map x y := by
  rw [presentedPerfectDGRightTensorIterated_map, presentedPerfectDGRightTensorComposite_map]
  exact presentedPerfectDGRightTensorIteration_transport A D E T
    x.1.2 y.1.2 x.2 y.2 x.1.1 y.1.1

/-- 元の二回右作用と入力横合成の右作用は、同じ三重 tensor 上の実 dg 関手で一致。 -/
lemma presentedPerfectDGRightTensorAction_comp :
    presentedPerfectDGRightTensorIterated A D E T =
      presentedPerfectDGRightTensorComposite A D E T := by
  apply presentedPerfectDGFunctor_ext A T (presentedPerfectDGRightTensorIterated_obj A D E T)
  intro x y
  exact presentedPerfectDGRightTensorIterated_map_transport A D E T x y

end SerrePositivity.KST.SConstruction
