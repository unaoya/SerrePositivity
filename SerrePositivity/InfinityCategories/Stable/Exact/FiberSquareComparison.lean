module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.CofiberSquareComparisonIso
public import SerrePositivity.InfinityCategories.Stable.IsomorphismFiberZero
public import SerrePositivity.InfinityCategories.F1.Categories.OppositeFunctorIso

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
namespace SerrePositivity.InfinityCategories.Stable.Exact.FiberComparison
open SerrePositivity.KST.LocalizingInvariants.FiberComparison

/-- 四角形全体の双対化は、元の二重反転の標準同型で戻る。 -/
lemma dualSquare_double {X : SSet.{u}} (F : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) :
    dualSquare (dualSquare F) ≫ (SSet.opFunctorCompOpFunctorIso.app X).hom = F := by
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
    {F G : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X} (e : FunctorIso F G) :
    FunctorIso (dualSquare F) (dualSquare G) := by
  let d := dualSquare (𝟙 ((Δ[1] : SSet.{u}) ⊗ Δ[1]))
  have h := e.op.precomp d
  simpa only [d, dualSquare, reverseGrid, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc] using h

/-- 同じ右辺を持つ二つの実 fiber 四角形は、全高次図式として同型。 -/
lemma nonempty_functorIso {X : SSet.{u}} [Quasicategory X] {x y : X _⦋0⦌}
    {f : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (s t : FiberSquare f) : Nonempty (FunctorIso s.square t.square) := by
  obtain ⟨e⟩ := nonempty_cofiberSquareFunctorIso s.opCofiber t.opCofiber
  have h := (dualFunctorIso e).postcomp (SSet.opFunctorCompOpFunctorIso.app X).hom
  change FunctorIso (dualSquare (dualSquare s.square) ≫ _)
    (dualSquare (dualSquare t.square) ≫ _) at h
  rw [dualSquare_double, dualSquare_double] at h
  exact ⟨h⟩

end SerrePositivity.InfinityCategories.Stable.Exact.FiberComparison

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Exact.FiberComparison.dualFunctorIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FiberComparison.dualFunctorIso := _root_.SerrePositivity.InfinityCategories.Stable.Exact.FiberComparison.dualFunctorIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FiberComparison.dualSquare_double := _root_.SerrePositivity.InfinityCategories.Stable.Exact.FiberComparison.dualSquare_double

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FiberComparison.nonempty_functorIso := _root_.SerrePositivity.InfinityCategories.Stable.Exact.FiberComparison.nonempty_functorIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FiberComparison.dualFunctorIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.FiberComparison.dualFunctorIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.FiberComparison.dualFunctorIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Stable.Exact.FiberComparison.dualFunctorIso._proof_2
