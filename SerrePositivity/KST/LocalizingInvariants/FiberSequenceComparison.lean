module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.FiberSquareComparison
public import SerrePositivity.KST.LocalizingInvariants.FiberSquareRelativeComparison
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroTriangleHoMap

/-!
概要：fiber 四角形の図式同型を、二辺を保つホモトピー圏の短複体同型へ送る。
方針：元の関手同型の三頂点での成分と二辺の自然性を使う。
規約：安定性を仮定しない。使われ方：K-5 の任意 fiber 列への π 長完全列の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.FiberComparison

/-- 全四角形の同型は三頂点と二辺を同時に保つ短複体の同型を与える。 -/
def shortComplexIso {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] (t d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroTriangle X)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso t.square d.square) : t.hoShortComplex ≅ d.hoShortComplex := by
  let a := e.toNatIso
  exact ShortComplex.isoMk
    (a.app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 0 0))
    (a.app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 0))
    (a.app (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoVertex (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])) 1 1))
    (a.hom.naturality (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoBottom (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])))).symm
    (a.hom.naturality (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.squareHoRight (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1])))).symm

/-- 同じ右辺の任意の fiber 列の比較。三対象と両射の同時自然性を含む。 -/
def fiberShortComplexIso {X : SSet.{u}} [Quasicategory X]
    [HasZeroMorphisms (hoFunctor.obj X)] {x y : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y} (s t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare f) :
    s.toZeroTriangle.hoShortComplex ≅ t.toZeroTriangle.hoShortComplex :=
  shortComplexIso s.toZeroTriangle t.toZeroTriangle (relativeFunctorIso s t).iso

end SerrePositivity.KST.LocalizingInvariants.FiberComparison
