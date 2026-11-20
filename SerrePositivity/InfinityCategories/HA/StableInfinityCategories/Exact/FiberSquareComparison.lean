module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberSquareComparisonIso
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsomorphismFiberZero
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIso

/-!
概要：同じ辺の二つの fiber 四角形の全図式の比較同型。
方針：安定性不要の cofiber 四角形比較を双対化し、二重反転を戻す。
規約：頂点だけの同型に弱めない。使われ方：K-5 の一般 fiber 長完全列の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.FiberComparison
end SerrePositivity.KST.LocalizingInvariants.FiberComparison
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact
open _root_.SerrePositivity.KST.LocalizingInvariants.FiberComparison

/-- 四角形全体の双対化は、元の二重反転の標準同型で戻る。 -/
lemma dualSquare_double {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare F) ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom = F := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, t⟩
  change F.app _ (_, _) = F.app _ (s, t)
  congr 1
  apply Prod.ext
  · apply stdSimplex.ext
    intro i
    change ((s i.rev.rev).rev).rev = s i
    simp only [Fin.rev_rev]
  · apply stdSimplex.ext
    intro i
    change ((t i.rev.rev).rev).rev = t i
    simp only [Fin.rev_rev]

/-- 双対化は全図式の関手同型を保つ。 -/
def dualFunctorIso {X : SSet.{u}} [Quasicategory X]
    {F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare F) (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare G) := by
  let d := _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1]))
  have h := e.op.precomp d
  simpa only [d, _root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseGrid, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc] using h

/-- 同じ右辺を持つ二つの実 fiber 四角形は、全高次図式として同型。 -/
lemma nonempty_functorIso {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s t : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.FiberSquare f) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso s.square t.square) := by
  obtain ⟨e⟩ := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.nonempty_cofiberSquareFunctorIso s.opCofiber t.opCofiber
  have h := (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.dualFunctorIso e).postcomp (SSet.opFunctorCompOpFunctorIso.app X).hom
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare s.square) ≫ _)
    (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.dualSquare t.square) ≫ _) at h
  rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.dualSquare_double, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.dualSquare_double] at h
  exact ⟨h⟩

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
