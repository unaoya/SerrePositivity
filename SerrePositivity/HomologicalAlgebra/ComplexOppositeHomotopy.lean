module
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.Homotopy

/-!
概要：添字を変えず形を反転する複体の反対化は、指定された鎖ホモトピーを保つ。
方針：成分を反対射に移し、ホモトピー方程式の二つの微分項の順を入れ替える。
規約：次数の符号を反転する余鎖複体の同値とは別。形 c は c.symm に移る。
使われ方：HA 1.2.4、G10 の重みの鎖分解から線形 end の余鎖分解への移送。
-/
@[expose] public noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c} {f g : K ⟶ L}

/-- 同じ添字の反対化で、元の二つの射のホモトピーを反対射のホモトピーへ移す。 -/
def complexOppositeHomotopy (h : Homotopy f g) :
    Homotopy ((HomologicalComplex.opFunctor C c).map f.op)
      ((HomologicalComplex.opFunctor C c).map g.op) where
  hom i j := (h.hom j i).op
  zero i j hij := by rw [h.zero j i hij, op_zero]
  comm i := by
    have hh := congrArg Quiver.Hom.op (h.comm i)
    change (f.f i).op = (K.d i (c.next i) ≫ h.hom (c.next i) i +
      h.hom i (c.prev i) ≫ L.d (c.prev i) i + g.f i).op at hh
    change (f.f i).op = (L.d (c.prev i) i).op ≫ (h.hom i (c.prev i)).op +
      (h.hom (c.next i) i).op ≫ (K.d i (c.next i)).op + (g.f i).op
    simpa only [op_add, op_comp, add_comm, add_left_comm, add_assoc] using hh

/-- 同じ形の反対化は鎖ホモトピー同値の指定射も保つ。 -/
def complexOppositeHomotopyEquiv (e : HomotopyEquiv K L) :
    HomotopyEquiv ((HomologicalComplex.opFunctor C c).obj (op L))
      ((HomologicalComplex.opFunctor C c).obj (op K)) where
  hom := (HomologicalComplex.opFunctor C c).map e.hom.op
  inv := (HomologicalComplex.opFunctor C c).map e.inv.op
  homotopyHomInvId := by
    simpa only [op_comp, op_id, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_id] using complexOppositeHomotopy e.homotopyInvHomId
  homotopyInvHomId := by
    simpa only [op_comp, op_id, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_id] using complexOppositeHomotopy e.homotopyHomInvId

end SerrePositivity.HomologicalAlgebra
