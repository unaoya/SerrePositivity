module
public import SerrePositivity.InfinityCategories.Derived.StandardCofiberTriangleFirstMorphisms
public import SerrePositivity.InfinityCategories.Derived.StandardCofiberTriangleThirdMorphism

/-! # 標準 cofiber 三角形の導来圏での像

概要：D3 の像を、元の鎖写像と cone 接続射から作る三角形と同型にする。
方針：三頂点の比較同型と、既に計算した三つの可換式を組み合わせる。
規約：安定 ∞ 圏の実 cofiber からの三角形。使われ方：D7 の三角性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Pretriangulated DifferentialGraded DGNerve
open scoped Simplicial ZeroObject
variable {S : Type u} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
variable {X Y : Semifree S}

/-- 零な直和成分を省いた標準 cone 三角形。 -/
def derivedStandardConeTriangle (f : X.val ⟶ Y.val) : Triangle (DerivedCategory (ModuleCat S)) :=
  Triangle.mk (DerivedCategory.Q.map f)
    (DerivedCategory.Q.map (pushoutInclusionB f (0 : X.val ⟶ 0)))
    (DerivedCategory.Q.map (CochainComplex.mappingCone.triangle
        (cofiberDifference f (0 : X.val ⟶ 0))).mor₃ ≫
      ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app X.val).hom)

/-- D3 は実際の標準 cofiber 三角形を標準 cone 三角形に写す。 -/
def derivedStandardCofiberTriangleImageIso (f : X.val ⟶ Y.val) :
    (derivedStableHomotopyEquivalence S).functor.mapTriangle.obj
        (cofiberTriangle (semifreeCofiberZeroTriangle f)
          (semifreeCofiberZeroTriangle_isCofiberSequence f)) ≅
      derivedStandardConeTriangle f :=
  Triangle.isoMk _ _ (derivedStandardCofiberSourceIso f) (derivedStandardCofiberMiddleIso f)
    (derivedStandardCofiberTargetIso f) (derivedStandardCofiberTriangle_comm₁ f)
    (derivedStandardCofiberTriangle_comm₂ f) (derivedStandardCofiberTriangle_comm₃ f)

end SerrePositivity.InfinityCategories
