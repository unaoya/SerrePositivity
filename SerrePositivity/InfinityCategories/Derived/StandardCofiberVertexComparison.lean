module
public import SerrePositivity.InfinityCategories.Derived.SemifreeCofiberZeroTriangle
public import SerrePositivity.InfinityCategories.Derived.StableHomotopyChainMap

/-! # 標準 cofiber 列の三頂点の導来比較

概要：実際の cofiber 三角形の三頂点の D3 像を、元の複体の Q 像と比較する。
方針：四角形の頂点同定を D3 で写し、Qh と Q の標準同型を合成する。
規約：第三頂点は標準 cone。使われ方：D7 の三角形の像の同型。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable {S : Type u} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]
variable {X Y : Semifree S}

/-- 標準 cofiber 列の第一頂点の導来比較。 -/
def derivedStandardCofiberSourceIso (f : X.val ⟶ Y.val) :
    (derivedStableHomotopyEquivalence S).functor.obj
      (semifreeCofiberZeroTriangle f).hoShortComplex.X₁ ≅ DerivedCategory.Q.obj X.val :=
  (derivedStableHomotopyEquivalence S).functor.mapIso
      (eqToIso (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex00 f))) ≪≫
    derivedStableHomotopyEquivalenceVertexIso S X

/-- 標準 cofiber 列の第二頂点の導来比較。 -/
def derivedStandardCofiberMiddleIso (f : X.val ⟶ Y.val) :
    (derivedStableHomotopyEquivalence S).functor.obj
      (semifreeCofiberZeroTriangle f).hoShortComplex.X₂ ≅ DerivedCategory.Q.obj Y.val :=
  (derivedStableHomotopyEquivalence S).functor.mapIso
      (eqToIso (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex10 f))) ≪≫
    derivedStableHomotopyEquivalenceVertexIso S Y

/-- 標準 cofiber 列の第三頂点の導来比較。 -/
def derivedStandardCofiberTargetIso (f : X.val ⟶ Y.val) :
    (derivedStableHomotopyEquivalence S).functor.obj
      (semifreeCofiberZeroTriangle f).hoShortComplex.X₃ ≅
      DerivedCategory.Q.obj (semifreeCofiberZeroObject f).val :=
  (derivedStableHomotopyEquivalence S).functor.mapIso
      (eqToIso (congrArg SSet.HomotopyCategory.mk (semifreeCofiberZeroTriangle_vertex11 f))) ≪≫
    derivedStableHomotopyEquivalenceVertexIso S (semifreeCofiberZeroObject f)

end SerrePositivity.InfinityCategories
