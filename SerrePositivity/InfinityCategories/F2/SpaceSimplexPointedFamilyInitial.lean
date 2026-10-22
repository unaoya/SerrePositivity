module

public import SerrePositivity.InfinityCategories.F2.SpaceSimplexPointedFamily
public import SerrePositivity.InfinityCategories.F2.SpaceSimplexSourceConeInitial
public import SerrePositivity.InfinityCategories.F2.PointedCoherentCosliceFiber

/-!
概要：元の全単体上の pointed 族の始点を、元の標準 fiber 比較へ厳密に同定する。
方針：初点 coslice の恒等点を既存の前合成の恒等式へ代入する。
規約：全反転 Hom 係数を保持。使われ方：同じ始点を固定した比較空間への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {n : ℕ} (s : SpaceInfinity.{u} _⦋n⦌)

/-- 全 coslice 族の初点は、同じ全反転 Hom の元の標準 fiber 比較そのもの。 -/
lemma spaceSimplexCoslicePointedFamily_initial :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))
        (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj
          (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op)) ≫
      spaceSimplexCoslicePointedFamily s =
    coherentCosliceFiberComparison pointKanObject (s.obj ⟨ULift.up 0⟩) ≫
      vertexFiberι (sliceUnderProjection (SSet.yonedaEquiv.symm
        (coherentNerveVertex pointKanObject)))
          (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)) := by
  rw [spaceSimplexCoslicePointedFamily, ← Category.assoc, lift_whiskerRight,
    SSet.const_comp, spaceSimplexSourceCone_initial_vertex]
  exact coherentCosliceSourcePrecomposition_identity pointKanObject (s.obj ⟨ULift.up 0⟩)

/-- 元の実 pointed 族の初点も、同じ元の標準 fiber 比較を厳密に保持する。 -/
lemma spaceSimplexPointedFamily_initial :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin (n + 1))))
        (𝟙 ((SSet.uliftFunctor.{u + 1, u}).obj
          (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op)) ≫
      spaceSimplexPointedFamily s =
    pointedCoherentFiberComparison (s.obj ⟨ULift.up 0⟩) ≫
      vertexFiberι pointedSpaceProjection (coherentNerveVertex (s.obj ⟨ULift.up 0⟩)) := by
  rw [spaceSimplexPointedFamily, ← Category.assoc, spaceSimplexCoslicePointedFamily_initial]
  exact (pointedCoherentCosliceIso_comparison (s.obj ⟨ULift.up 0⟩)).symm

end SerrePositivity.InfinityCategories.F2
