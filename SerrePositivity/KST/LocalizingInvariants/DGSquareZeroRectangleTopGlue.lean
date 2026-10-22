module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRectangleOfHom
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeGlueContour

/-!
概要：元の中央経路に同定した正方形へ、元の三経路貼合せの両側を接続する。
方針：中央辺の全経路の一致から角を同定し、同じ両側経路を端点だけ移送する。
規約：両側経路そのものを変更しない。使われ方：Γ の三経路貼合せと輪郭の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RectangleOfHom
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} (N : Bimod B B)
  (H : W ⟶ DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)))
  (q : W ⟶ B) {x y a b : W ⟶ algebra B N} (v : RelativeWitness q N a b)
  (hTop : H ≫ DGAlgebra.Path.source R (DGAlgebra.Path.algebra R (algebra B N)) = v.hom)

include v hTop

lemma topSource_eq : corner00 N H = a :=
  (congrArg (fun k => k ≫ DGAlgebra.Path.source R (algebra B N)) hTop).trans v.source_eq

lemma topTarget_eq : corner01 N H = b :=
  (congrArg (fun k => k ≫ DGAlgebra.Path.target R (algebra B N)) hTop).trans v.target_eq

def towardTopSource (t : RelativeWitness q N x a) : RelativeWitness q N x (corner00 N H) where
  hom := t.hom
  source_eq := t.source_eq
  target_eq := t.target_eq.trans (topSource_eq N H q v hTop).symm
  projection_eq := t.projection_eq

def towardTopTarget (s : RelativeWitness q N y b) : RelativeWitness q N y (corner01 N H) where
  hom := s.hom
  source_eq := s.source_eq
  target_eq := s.target_eq.trans (topTarget_eq N H q v hTop).symm
  projection_eq := s.projection_eq

variable (hbase : H ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
  (q ≫ DGAlgebra.Path.diagonal R B) ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R B))
  (t : RelativeWitness q N x a) (s : RelativeWitness q N y b)

/-- 元の三経路貼合せを保持した輪郭比較。 -/
def topGlueSquare :
    let t' := towardTopSource N H q v hTop t
    let s' := towardTopTarget N H q v hTop s
    RelativeWitnessSquare
      (((t.comp v).comp s.reverse).comp (s'.comp (innerTarget N H q hbase)))
      (t'.comp ((innerSource N H q hbase).comp (outerTarget N H q hbase))) := by
  let t' := towardTopSource N H q v hTop t
  let s' := towardTopTarget N H q v hTop s
  let z := (rectangle N H q hbase).glueContourSquare t' s'
  have hg : ((t'.comp (outerSource N H q hbase)).comp s'.reverse).hom =
      ((t.comp v).comp s.reverse).hom := by
    apply Mon.Hom.ext
    simp only [RelativeWitness.comp_hom_linear, RelativeWitness.reverse_hom_linear]
    change (t.hom.hom - (corner00 N H ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom +
      (H ≫ DGAlgebra.Path.source R (DGAlgebra.Path.algebra R (algebra B N))).hom) -
      (corner01 N H ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom +
        ((y ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom - s.hom.hom +
          (corner01 N H ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom) =
      (t.hom.hom - (a ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom + v.hom.hom) -
        (b ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom +
          ((y ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom - s.hom.hom +
            (b ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom)
    rw [topSource_eq N H q v hTop, hTop]
    abel
  have hc :
      (((t'.comp (outerSource N H q hbase)).comp s'.reverse).comp
        (s'.comp (innerTarget N H q hbase))).hom =
      (((t.comp v).comp s.reverse).comp (s'.comp (innerTarget N H q hbase))).hom := by
    apply Mon.Hom.ext
    rw [RelativeWitness.comp_hom_linear
      ((t'.comp (outerSource N H q hbase)).comp s'.reverse)
      (s'.comp (innerTarget N H q hbase)), hg,
      RelativeWitness.comp_hom_linear ((t.comp v).comp s.reverse)
        (s'.comp (innerTarget N H q hbase))]
  exact RelativeWitnessSquare.replacePaths z hc rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RectangleOfHom
