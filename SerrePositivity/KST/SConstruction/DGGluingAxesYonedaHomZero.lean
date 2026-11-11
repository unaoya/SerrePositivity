module
public import SerrePositivity.KST.SConstruction.DGGluingAxesRepresentableCofiber
public import SerrePositivity.KST.SConstruction.DGClosedTriangleHomIsoLiftModule

/-! # 元の二軸代表間の全 Hom の実零性
概要：右軸代表から左軸代表への全 Hom end は、元の半直交 Hom 同型により実零となる。
方針：元の Yoneda 鎖同型と各次数の評価を使う。
規約：全整数次数を保持。使われ方：二軸 cofiber の上下二セルの微分式の反映。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "A" => dgGluingRightAxisObject R C D M zc X.right
local notation "B" => dgGluingLeftAxisObject R C D M zd X.left
include hc hd

/-- 元の右軸代表から左軸代表への全 Hom end は実零対象。 -/
lemma dgGluingAxesYonedaHom_isZero :
    IsZero (homObject R (RightModule R G) (representable R A) (representable R B)) :=
  (dgGluingAxes_right_left_hom_isZero R C D M zc hc zd hd X.right X.left).of_iso
    (dgYonedaIso R A (representable R B))

/-- 同じ元の全 Hom end の各整数次数には、元が一つしかない。 -/
lemma dgGluingAxesYonedaHom_subsingleton (n : ℤ) :
    Subsingleton ((homObject R (RightModule R G)
      (representable R A) (representable R B)).X n) :=
  ModuleCat.subsingleton_of_isZero
    ((HomologicalComplex.eval (ModuleCat R) (.up ℤ) n).map_isZero
      (dgGluingAxesYonedaHom_isZero R C D M zc hc zd hd X))

end SerrePositivity.KST.SConstruction
