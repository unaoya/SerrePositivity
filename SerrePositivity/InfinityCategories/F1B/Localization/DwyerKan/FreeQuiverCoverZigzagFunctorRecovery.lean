module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.FreeQuiverCoverZigzagRecovery

/-!
# 元の全縦射を含む両合成関手の回収

概要：持ち上げと射影の両合成は元の恒等関手に厳密に一致する。
方針：対象の回収と射影の忠実性で元の全縦成分を照合する。
規約：射の文字列だけでなく元の全成分の等式を使う。
使われ方：固定語ごとの元の値の fiber の圏同値。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) {w : Word} {Y : Paths Q}
  {β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y}

lemma valueFiber_hom_hext {S T S' T' : ZigzagValueFiber A w Y β}
    (hS : S = S') (hT : T = T') (f : S ⟶ T) (g : S' ⟶ T')
    (h : HEq f.hom g.hom) : HEq f g := by
  cases hS
  cases hT
  exact heq_of_eq (ObjectProperty.hom_ext (zigzagValueProperty A w Y β) (eq_of_heq h))

lemma zigzagLiftFunctor_fiberProjection :
    letI := quiver A
    zigzagLiftFunctor A w Y β ⋙ zigzagFiberProjection A w Y β =
      𝟭 (ZigzagValueFiber A w Y β) := by
  let := quiver A
  apply CategoryTheory.Functor.hext
    (F := zigzagLiftFunctor A w Y β ⋙ zigzagFiberProjection A w Y β)
    (G := 𝟭 (ZigzagValueFiber A w Y β))
  · exact zigzagFiberProjection_lift_obj A
  · intro S T f
    apply valueFiber_hom_hext A (zigzagFiberProjection_lift_obj A S)
      (zigzagFiberProjection_lift_obj A T)
    exact Zigzag.hom_hext (zigzagLift_projection A S) (zigzagLift_projection A T)
      _ _ (fun j => heq_of_eq (zigzagLiftMap_app_projection A f j))

lemma zigzagFiberProjection_liftFunctor :
    letI := quiver A
    zigzagFiberProjection A w Y β ⋙ zigzagLiftFunctor A w Y β =
      𝟭 (Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
        ((Paths.of (Vertex A)).obj (root A))
        ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β))) := by
  let := quiver A
  apply CategoryTheory.Functor.hext
    (F := zigzagFiberProjection A w Y β ⋙ zigzagLiftFunctor A w Y β)
    (G := 𝟭 (Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β))))
  · exact zigzagLift_fiberProjection_obj A
  · intro S T f
    apply Zigzag.hom_hext (zigzagLift_fiberProjection_obj A S)
      (zigzagLift_fiberProjection_obj A T)
    intro j
    exact pathProjection_hom_hext A
      (congrArg (fun Z => Z.vertex j) (zigzagLift_fiberProjection_obj A S))
      (congrArg (fun Z => Z.vertex j) (zigzagLift_fiberProjection_obj A T)) _ _
      (heq_of_eq (zigzagLiftMap_app_projection A ((zigzagFiberProjection A w Y β).map f) j))

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
