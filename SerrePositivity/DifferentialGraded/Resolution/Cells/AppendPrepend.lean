module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathAction
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendRecursion
public import SerrePositivity.DifferentialGraded.Complexes.TensorJoinRightAction

/-! # 任意次数cell path：AppendPrepend -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

/-- 元のHomを先頭へ作用させる操作と有限path連結は結合する。 -/
@[reassoc] lemma appendMap_prepend (w v : List I) (x y z t : D) :
    (C.prependMap A D I w x y z ▷ C.term A D I v z t) ≫ C.appendMap A D I w v x z t =
    (α_ (homObject A D x y) (C.term A D I w y z) (C.term A D I v z t)).hom ≫
      (homObject A D x y) ◁ C.appendMap A D I w v y z t ≫ C.prependMap A D I (w ++ v) x y t := by
  cases w with
  | nil => exact C.prependMap_assoc A D I v x y z t
  | cons b w =>
    simpa only [prependMap, appendMap, term, tensorHom_id, List.cons_append] using
      tensorJoin_right_action (homObject A D x y) (homObject A D y (C.source b))
        (homObject A D x (C.source b)) (C.generator A D I b ⊗ C.term A D I w (C.target b) z)
        (C.term A D I v z t) (C.generator A D I b ⊗ C.term A D I (w ++ v) (C.target b) t)
        (eComp (Complex A) x y (C.source b))
        ((α_ (C.generator A D I b) (C.term A D I w (C.target b) z) (C.term A D I v z t)).hom ≫
          (C.generator A D I b) ◁ C.appendMap A D I w v (C.target b) z t)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
