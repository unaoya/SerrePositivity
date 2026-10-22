module

public import SerrePositivity.InfinityCategories.F2.CosliceOppositeHomComposition
public import SerrePositivity.InfinityCategories.F2.PointedCoherentCosliceFiber

/-!
概要：全反転 Hom の二係数合成を実 pointed space の同じ係数作用へ戻す。
方針：coslice 全体の合成則と一点表示の正規化を合成する。
規約：射を固定せず全 Hom の単体と全独立係数を保持する。
使われ方：元の指定精密化の反転の全 Hom 作用と長辺値式の照合。
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

/-- 全 Hom の二係数合成は元の実 pointed space の同じ全係数作用。 -/
lemma pointedCoherentSourcePrecomposition_hom (K L : KanObject.{u}) :
    ((coherentCosliceFiberComparison K L ≫ vertexFiberι
      (sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex K)))
        (coherentNerveVertex L)) ▷
          (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject K).op) ≫
      coherentCosliceSourcePrecomposition pointKanObject K ≫ pointedCoherentCosliceIso.hom =
    (uliftTensorIso (SimplicialCategory.sHom K L).op
      (SimplicialCategory.sHom pointKanObject K).op).inv ≫
      (SSet.uliftFunctor.{u + 1, u}).map (oppositeHomPrecomposition pointKanObject K L) ≫
        pointedCoherentFiberComparison L ≫
          vertexFiberι pointedSpaceProjection (coherentNerveVertex L) := by
  have h := congrArg (fun f ↦ f ≫ pointedCoherentCosliceIso.hom)
    (coherentCosliceSourcePrecomposition_hom
      ((Functor.const (Discrete PUnit.{u + 1})).obj L) pointKanObject K
        (⟨PUnit.unit⟩ : Discrete PUnit.{u + 1}))
  simp only [Category.assoc] at h
  rw [← pointedCoherentCosliceIso_comparison] at h
  exact h

end SerrePositivity.InfinityCategories.F2
