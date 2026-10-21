module

public import SerrePositivity.EInfinity.Hammock.FreeQuiverCoverZigzagFunctorRecovery
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Category.Cat

/-!
# 元の値の fiber と被覆の固定端点 zigzag 圏の同型

概要：元の二つの関手が厳密に逆である圏同型を構成する。
方針：証明済みの両合成の恒等性をそのまま使う。
規約：同型の両関手は元の持ち上げと元の射影に一致する。
使われ方：全語の nerve 図式の同型。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.FreeQuiverCover
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (A : Q) (w : Word) (Y : Paths Q)
  (β : (Quiver.FreeGroupoid.of Q).obj A ⟶ positiveEvaluation.obj Y)

def zigzagFiberEquivalence :
    letI := quiver A
    ZigzagValueFiber A w Y β ≌ Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
      ((Paths.of (Vertex A)).obj (root A))
      ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β)) := by
  letI := quiver A
  exact CategoryTheory.Equivalence.mk (zigzagLiftFunctor A w Y β) (zigzagFiberProjection A w Y β)
    (eqToIso (zigzagLiftFunctor_fiberProjection A).symm)
    (eqToIso (zigzagFiberProjection_liftFunctor A))

def zigzagFiberCategoryIso :
    letI := quiver A
    Cat.of (ZigzagValueFiber A w Y β) ≅
      Cat.of (Zigzag (⊤ : MorphismProperty (Paths (Vertex A))) w
        ((Paths.of (Vertex A)).obj (root A))
        ((Paths.of (Vertex A)).obj (fiberEndpoint A Y β))) := by
  letI := quiver A
  exact
    { hom := (zigzagLiftFunctor A w Y β).toCatHom
      inv := (zigzagFiberProjection A w Y β).toCatHom
      hom_inv_id := by apply Cat.Hom.ext; exact zigzagLiftFunctor_fiberProjection A
      inv_hom_id := by apply Cat.Hom.ext; exact zigzagFiberProjection_liftFunctor A }

end SerrePositivity.EInfinity.Hammock.FreeQuiverCover
