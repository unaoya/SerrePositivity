module
public import SerrePositivity.KST.SConstruction.DGGluingAxesYonedaHomotopyIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TriangleThirdTransport
public import SerrePositivity.DifferentialGraded.Module.MaurerCartanTriangulated

/-! # 元の二軸射を保持する実 Yoneda distinguished 三角形
概要：右軸・元の対象・左軸の同じ三代表を持つ distinguished 三角形を構成する。
方針：元の右軸射の標準円錐三角形を、同じ円錐比較の実同型で移す。
規約：最初の二射は元の二軸射の像。使われ方：実 dg 二軸分解と商の生成性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Pretriangulated
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "Q" => moduleToHomotopy R G

/-- 同じ右軸・元の対象・左軸の代表加群を三頂点とする実三角形。 -/
def dgGluingAxesYonedaTriangle : Triangle (ModuleHomotopyCategory R G) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleThirdTransport
    (moduleHomotopyConeTriangle R G (dgGluingAxesYonedaRightMap R C D M zc hc X))
    (dgGluingAxesYonedaConeHomotopyIso R C D M zc hc zd hd X)

/-- 同じ実二軸三角形は distinguished である。 -/
lemma dgGluingAxesYonedaTriangle_distinguished :
    dgGluingAxesYonedaTriangle R C D M zc hc zd hd X ∈
      distTriang (ModuleHomotopyCategory R G) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleThirdTransport_distinguished _
    (moduleHomotopyConeTriangle_distinguished R G
      (dgGluingAxesYonedaRightMap R C D M zc hc X)) _

/-- 同じ三角形の第一射は、元の右軸包含の Yoneda 像そのもの。 -/
lemma dgGluingAxesYonedaTriangle_mor₁ :
    (dgGluingAxesYonedaTriangle R C D M zc hc zd hd X).mor₁ =
      (Q).map (dgGluingAxesYonedaRightMap R C D M zc hc X) := rfl

/-- 同じ三角形の第二射は、元の左軸射影の Yoneda 像を厳密に回収する。 -/
lemma dgGluingAxesYonedaTriangle_mor₂ :
    (dgGluingAxesYonedaTriangle R C D M zc hc zd hd X).mor₂ =
      (Q).map (dgGluingAxesYonedaLeftMap R C D M zd hd X) :=
  dgGluingAxesYonedaConeHomotopyIso_inr R C D M zc hc zd hd X

/-- 同じ三角形の第三対象は、元の左軸の代表加群そのもの。 -/
lemma dgGluingAxesYonedaTriangle_obj₃ :
    (dgGluingAxesYonedaTriangle R C D M zc hc zd hd X).obj₃ =
      (Q).obj (ForgetEnrichment.of (Complex R)
        (representable R (dgGluingLeftAxisObject R C D M zd X.left))) := rfl

end SerrePositivity.KST.SConstruction
