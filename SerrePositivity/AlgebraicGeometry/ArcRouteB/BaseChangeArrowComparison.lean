module

public import SerrePositivity.AlgebraicGeometry.ArcRouteB.Definitions

/-!
概要：環の射からの底変換と、B1のUnderの底変換を同じArrowとして比較する。
方針：構造射から派生した代数構造と元の代数構造の既存の等式を、Arrowの段で処理する。
規約：選ばれたČech余極限の内部を書き換えず、同じ係数・元の射を保つ。
使われ方：2iの照合法則L02、普遍貼り合わせと普遍超積への係数移送。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory
namespace SerrePositivity.AlgebraicGeometry.ArcRouteB

set_option backward.isDefEq.respectTransparency false

/-- 照合法則L02：元の係数の環射とUnderからの同じ底変換の指定Arrow同型。 -/
def arcBaseChangeArrowIso {A : Type u} [CommRing A]
    (B : Under (CommRingCat.of A)) (D : Type u) [CommRing D] [Algebra A D] :
    Arrow.mk (CommRingCat.ofHom (arcBaseChangeHom B.hom.hom (algebraMap A D))) ≅
      Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of D)).obj B).hom := by
  let F (aD : Algebra A D) : Arrow CommRingCat.{u} :=
    letI := aD
    Arrow.mk ((CommRingCat.tensorProd (CommRingCat.of A) (CommRingCat.of D)).obj B).hom
  exact eqToIso (congrArg F (toAlgebra_algebraMap (R := A) (S := D)))

end SerrePositivity.AlgebraicGeometry.ArcRouteB
