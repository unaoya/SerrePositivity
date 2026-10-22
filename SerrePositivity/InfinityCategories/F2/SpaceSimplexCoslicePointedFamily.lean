module

public import SerrePositivity.InfinityCategories.F2.SpaceSimplexSourceCone

/-!
概要：元の任意の Space 単体の上に、反転 Hom 全体の coslice 族を構成する。
方針：元の初点退化の coslice 単体に、既存の全 Hom 前合成を作用させる。
規約：元の全図式と全係数を保持。使われ方：三つの面を同じ実際の族で照合する。
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

/-- 同じ元の初点からの全反転 Hom 係数を、pointed-space と同じ宇宙に置く。 -/
abbrev spaceSimplexPointedCoefficients : SSet.{u + 1} :=
  (SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op

/-- 元の全標準単体の上で、反転 Hom 全体の係数による実 coslice 前合成。 -/
def spaceSimplexCoslicePointedFamily :
    (Δ[n] : SSet.{u + 1}) ⊗ (SSet.uliftFunctor.{u + 1, u}).obj
      (SimplicialCategory.sHom pointKanObject (s.obj ⟨ULift.up 0⟩)).op ⟶
      sliceUnder (SSet.yonedaEquiv.symm (coherentNerveVertex pointKanObject)) :=
  (SSet.yonedaEquiv.symm (spaceSimplexSourceCone s) ▷ _) ≫
    coherentCosliceSourcePrecomposition pointKanObject (s.obj ⟨ULift.up 0⟩)

/-- 全 Hom 族の射影は、係数を忘れた元の全 Space 単体そのもの。 -/
lemma spaceSimplexCoslicePointedFamily_projection :
    spaceSimplexCoslicePointedFamily s ≫
      sliceUnderProjection (SSet.yonedaEquiv.symm (coherentNerveVertex pointKanObject)) =
        fst _ _ ≫ SSet.yonedaEquiv.symm s := by
  rw [spaceSimplexCoslicePointedFamily, Category.assoc,
    coherentCosliceSourcePrecomposition_over, ← Category.assoc, whiskerRight_fst,
    Category.assoc, spaceSimplexSourceCone_map_projection]

/-- 対角の同じ全係数で前合成した実 coslice の座標は、元の pointed 拡張単体。 -/
lemma spaceSimplexCoslicePointedFamily_diagonal_coordinates
    (p : (Δ[n] : SSet.{u}) ⟶ (SimplicialCategory.sHom pointKanObject
      (s.obj ⟨ULift.up 0⟩)).op) :
    coherentCosliceSourceSimplex pointKanObject
      ((spaceSimplexCoslicePointedFamily s).app (Opposite.op ⦋n⦌)
        (SSet.yonedaEquiv (𝟙 Δ[n]), ULift.up (SSet.yonedaEquiv p))) =
          spaceSimplexPointedAugmentation s p := by
  change coherentCosliceSourceSimplex pointKanObject
    (cosliceSourcePrecompositionSimplex pointKanObject (s.obj ⟨ULift.up 0⟩)
      ((SSet.yonedaEquiv.symm (spaceSimplexSourceCone s)).app (Opposite.op ⦋n⦌)
        (SSet.yonedaEquiv (𝟙 Δ[n]))) (SSet.yonedaEquiv p)) = _
  rw [SSet.yonedaEquiv_symm_app_id]
  change SSet.yonedaEquiv ((leftPointStdSimplexIso n).inv ≫
    ((leftPointStdSimplexIso n).hom ≫ SSet.yonedaEquiv.symm
      (coneInitialFixedSimplex pointKanObject
        (cosliceInitialCoordinates (s.obj ⟨ULift.up 0⟩) (spaceSimplexSourceCone s))
          (SSet.yonedaEquiv.symm (SSet.yonedaEquiv p))))) = _
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply,
    spaceSimplexSourceCone_initialCoordinates, Equiv.symm_apply_apply]
  rfl

end SerrePositivity.InfinityCategories.F2
