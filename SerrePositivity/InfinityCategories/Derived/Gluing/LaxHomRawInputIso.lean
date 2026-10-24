module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomInputTransport
public import SerrePositivity.InfinityCategories.Derived.Gluing.UniversePinchedComplexIso
public import SerrePositivity.InfinityCategories.Derived.Gluing.CommonComplexUniverseIso
public import SerrePositivity.InfinityCategories.F2.CatInfinity.PinchedHomTensorIso
/-!
概要：正本 lax Hom 標的の第二座標を元の左右 Hom 複体模型の積へ厳密に移す。
方針：端点輸送、積の pinched Hom 同型、一般宇宙の複体模型同型を合成する。
規約：対象・複体・線形成分と左右の順序を変えない。
使われ方：正本標的と入力付き四座標標的の同じ二入力を照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory DifferentialGraded DGNerve
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)

lemma dgGluingUniverseLeftNerve_vertex (X : DGGluingObject R C D M) :
    (dgGluingUniverseLeftNerve R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex X)) = ULift.up (Simplex.vertex X.left) :=
  dgGluingUniverseNerveMap_vertex.{u, max u v w, v, max (u + 1) v w} (dgGluingLeft R C D M) X

lemma dgGluingUniverseRightNerve_vertex (X : DGGluingObject R C D M) :
    (dgGluingUniverseRightNerve R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex X)) = ULift.up (Simplex.vertex X.right) :=
  dgGluingUniverseNerveMap_vertex.{u, max u v w, w, max (u + 1) v w} (dgGluingRight R C D M) X

def dgGluingLaxHomLeftRawInputIso :=
  dgGluingUniversePinchedComplexIso.{u,v,max (u + 1) v w} R C X.left Y.left ≪≫
    dgGluingCommonComplexPinchedUniverseIso.{u,v,max u v w,max (u + 1) v w}
      (homObject R C X.left Y.left)

def dgGluingLaxHomRightRawInputIso :=
  dgGluingUniversePinchedComplexIso.{u,w,max (u + 1) v w} R D X.right Y.right ≪≫
    dgGluingCommonComplexPinchedUniverseIso.{u,w,max u v w,max (u + 1) v w}
      (homObject R D X.right Y.right)

def dgGluingLaxHomRawInputIso :=
  dgGluingLaxHomInputEndpointIso R C D M X Y ≪≫
    F2.pinchedHomTensorIso
      ((lift (dgGluingUniverseLeftNerve R C D M) (dgGluingUniverseRightNerve R C D M)).app
        (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex X)))
      ((lift (dgGluingUniverseLeftNerve R C D M) (dgGluingUniverseRightNerve R C D M)).app
        (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex Y))) ≪≫
      tensorIso
        (pinchedEndpointIso (dgGluingUniverseLeftNerve_vertex R C D M X)
          (dgGluingUniverseLeftNerve_vertex R C D M Y) ≪≫
            dgGluingLaxHomLeftRawInputIso R C D M X Y)
        (pinchedEndpointIso (dgGluingUniverseRightNerve_vertex R C D M X)
          (dgGluingUniverseRightNerve_vertex R C D M Y) ≪≫
            dgGluingLaxHomRightRawInputIso R C D M X Y)
end SerrePositivity.InfinityCategories
