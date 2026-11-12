module
public import SerrePositivity.KST.SConstruction.DGGluingAxesYonedaQuasiIso
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.TriangleThirdTransport

/-! # 元の二軸代表の指定導来圏内の三角形
概要：元の二軸代表と元の二射を、同じ加群導来圏の distinguished 三角形にする。
方針：D の既存導来関手で同じ円錐比較を可逆にし、標準円錐三角形を移す。
規約：商や局所化の普遍性は新設しない。使われ方：具体的 gluing の Perfect 生成性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits Pretriangulated DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "Q" => moduleToDerived R G

/-- 元の同じ Yoneda 円錐比較は、D の既存導来関手で可逆となる。 -/
def dgGluingAxesDerivedConeIso :
    (Q).obj (moduleCone R G (dgGluingAxesYonedaRightMap R C D M zc hc X)) ≅
      (Q).obj (ForgetEnrichment.of (Complex R)
        (representable R (dgGluingLeftAxisObject R C D M zd X.left))) := by
  let := moduleToDerived_inverts R G
    (dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X)
    (dgGluingAxesYonedaConeComparison_moduleQuasiIso R C D M zc hc zd hd X)
  exact asIso ((Q).map (dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X))

/-- 同じ三代表を頂点とする、指定導来圏の実三角形。 -/
def dgGluingAxesDerivedTriangle : Triangle (DerivedModuleCategory R G) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleThirdTransport
    (moduleDerivedConeTriangle R G (dgGluingAxesYonedaRightMap R C D M zc hc X))
    (dgGluingAxesDerivedConeIso R C D M zc hc zd hd X)

/-- 元の二軸の同じ導来三角形は distinguished。 -/
lemma dgGluingAxesDerivedTriangle_distinguished :
    dgGluingAxesDerivedTriangle R C D M zc hc zd hd X ∈
      distTriang (DerivedModuleCategory R G) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleThirdTransport_distinguished _
    (moduleDerivedConeTriangle_distinguished R G
      (dgGluingAxesYonedaRightMap R C D M zc hc X)) _

/-- 同じ導来三角形の第一射は、元の右軸包含の像そのもの。 -/
lemma dgGluingAxesDerivedTriangle_mor₁ :
    (dgGluingAxesDerivedTriangle R C D M zc hc zd hd X).mor₁ =
      (Q).map (dgGluingAxesYonedaRightMap R C D M zc hc X) := rfl

/-- 同じ導来三角形の第二射は、元の左軸射影の像を厳密に回収する。 -/
lemma dgGluingAxesDerivedTriangle_mor₂ :
    (dgGluingAxesDerivedTriangle R C D M zc hc zd hd X).mor₂ =
      (Q).map (dgGluingAxesYonedaLeftMap R C D M zd hd X) := by
  change (Q).map (moduleConeInr R G (dgGluingAxesYonedaRightMap R C D M zc hc X)) ≫
    (Q).map (dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X) = _
  rw [← Functor.map_comp, dgGluingAxesYonedaConeComparison_inr]

end SerrePositivity.KST.SConstruction
