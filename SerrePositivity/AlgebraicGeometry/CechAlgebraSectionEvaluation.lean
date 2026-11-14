module

public import SerrePositivity.AlgebraicGeometry.CechAlgebraH0

/-!
概要：適合切断の部分代数から、各零次タプルの標準開の代数への評価。
方針：元の切断族の成分を取り、成分ごとの代数演算を用いる。
規約：Čech H⁰ 上の環構造を新しく定義しない。
使われ方：基底の中心から閉厚化の各標準開への実際の写像。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R : Type u} [CommRing R] {ι : Type} [DecidableEq ι]

/-- 適合切断を指定した標準開で評価する代数準同型。 -/
def fullAlgebraCechSectionEvaluation (D : Finset ι ⥤ CommAlgCat.{u} R) (t : Fin 1 → ι) :
    fullAlgebraCechEqualizer D →ₐ[R] D.obj (cechTupleSupport t) where
  toFun s := s.val t
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end SerrePositivity.AlgebraicGeometry
