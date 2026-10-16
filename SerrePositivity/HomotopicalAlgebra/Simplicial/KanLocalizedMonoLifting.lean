module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoRelativeHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanMonoStrictExtension
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension

/-! # Localized mono equivalences lift against Kan fibrations with Kan base

The extension and both endpoint corrections retain the original square.
No model structure or additional weak-equivalence class is assumed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SerrePositivity.SimplicialModel.KanLocalizedMonoLifting
variable {A T E B : SSet.{v}} (i : A ⟶ T) [Mono i]
  (hi : IsIso (AnodyneHomotopy.anodyneQ.map i))
  (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p)
  (hB : SSet.modelCategoryQuillen.J.rlp (terminal.from B))

include hi hp hB in
lemma hasLiftingProperty : HasLiftingProperty i p := by
  have : Fibration p := (SSet.modelCategoryQuillen.fibration_iff _).mpr hp
  have : Fibration (terminal.from B) := (SSet.modelCategoryQuillen.fibration_iff _).mpr hB
  have : SSet.KanComplex B := (isFibrant_iff B).mpr inferInstance
  have : SSet.KanComplex E := isFibrant_of_fibration p
  have hE : SSet.modelCategoryQuillen.J.rlp (terminal.from E) :=
    (SSet.modelCategoryQuillen.fibration_iff _).mp inferInstance
  constructor
  intro a b sq
  obtain ⟨g, hg⟩ := KanMonoStrictExtension.exists_extension i hE hi a
  let H₀ : SSet.Homotopy (i ≫ (g ≫ p)) (i ≫ b) :=
    { h := fst A (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ a ≫ p
      h₀ := by
        rw [← Category.assoc, AnodyneHomotopy.endpoint_projection_zero, Category.id_comp]
        exact (congrArg (fun f => f ≫ p) hg).symm.trans (Category.assoc _ _ _)
      h₁ := by
        rw [← Category.assoc, AnodyneHomotopy.endpoint_projection_one, Category.id_comp]
        exact sq.w
      rel := by
        apply NatTrans.ext
        funext n
        exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property) }
  obtain ⟨H, hH⟩ := KanMonoRelativeHomotopy.exists_extension i hi hB (g ≫ p) b H₀
  let Ha : SSet.Homotopy (i ≫ g) a :=
    { h := fst A (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ a
      h₀ := by
        rw [← Category.assoc, AnodyneHomotopy.endpoint_projection_zero, Category.id_comp]
        exact hg.symm
      h₁ := by
        rw [← Category.assoc, AnodyneHomotopy.endpoint_projection_one, Category.id_comp]
        rfl
      rel := by
        apply NatTrans.ext
        funext n
        exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property) }
  have hHa : Ha.h ≫ p = i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ H.h := by
    rw [hH]
    rfl
  obtain ⟨g', hg', ⟨V, _, hVp⟩⟩ := KanFibrationEndpointExtension.exists_from_zero p hp i g a Ha
    H.h H.h₀.symm hHa
  refine CommSq.HasLift.mk' { l := g', fac_left := hg', fac_right := ?_ }
  calc
    g' ≫ p = (SSet.ι₁ ≫ V.h) ≫ p := congrArg (fun f => f ≫ p) V.h₁.symm
    _ = SSet.ι₁ ≫ (V.h ≫ p) := Category.assoc _ _ _
    _ = SSet.ι₁ ≫ H.h := congrArg (fun f => SSet.ι₁ ≫ f) hVp
    _ = b := H.h₁

end SerrePositivity.SimplicialModel.KanLocalizedMonoLifting
