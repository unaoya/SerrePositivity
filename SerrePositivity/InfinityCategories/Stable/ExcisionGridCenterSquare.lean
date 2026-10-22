module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridCenterSpanShapeIso

/-!
概要：中央の実正方形と同じ span の辺・頂点の厳密な比較。
方針：同じ実図式の native 余錐と頂点を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の中央面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {P : Type u} [PartialOrder P]

def excisionGridCenterSquare : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶
    nerve ExcisionGridCoreIndex.{u} where
  app n := ↾fun s ↦
    (⟨fun k ↦ excisionGridCorePoint ((stdSimplex.objEquiv s.1).toOrderHom k).succ
        ((stdSimplex.objEquiv s.2).toOrderHom k).succ,
      fun _ _ h ↦ excisionGridCorePoint_le
        (Nat.add_le_add_right ((stdSimplex.objEquiv s.1).toOrderHom.monotone h) 1)
        (Nat.add_le_add_right ((stdSimplex.objEquiv s.2).toOrderHom.monotone h) 1)⟩ :
      Fin (n.unop.len + 1) →o ExcisionGridCoreIndex.{u}).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

lemma excisionGridCenterSpanShapeIso_projection :
    excisionGridCenterSpanShapeIso.{u}.hom ≫
      (fullSubcomplexOnVertices (nerve ExcisionGridPastIndex.{u})
        (fun v ↦ IsExcisionGridCenterSpan (nerveEquiv v))).ι ≫
          nerveMap (posetSubtypeInclusion IsExcisionGridPast) =
      pushoutSpan excisionGridCenterSquare := by
  change pastingRightSpanIso.hom ≫ excisionGridPastingToCenterSpan ≫
    (posetSubtypeNerveIso IsExcisionGridCenterSpan).hom ≫
      (fullSubcomplexOnVertices (nerve ExcisionGridPastIndex.{u})
        (fun v ↦ IsExcisionGridCenterSpan (nerveEquiv v))).ι ≫
          nerveMap (posetSubtypeInclusion IsExcisionGridPast) = _
  rw [← Category.assoc (posetSubtypeNerveIso IsExcisionGridCenterSpan).hom,
    posetSubtypeNerveIso_hom_ι]
  apply horn₂₀.isPushout.hom_ext
  · rw [← Category.assoc horn₂₀.ι₀₁ pastingRightSpanIso.hom]
    change (horn₂₀.ι₀₁ ≫ pastingRightSpanFromHorn) ≫ _ = _
    rw [pastingRightSpanFromHorn_left]
    dsimp only [pushoutSpan]
    rw [← Category.assoc horn₂₀.ι₀₁ spanSquareBoundary, spanSquareBoundary_bottomEdge]
    apply thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply Subtype.ext <;> apply Subtype.ext <;> apply ULift.ext <;>
      apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide
  · rw [← Category.assoc horn₂₀.ι₀₂ pastingRightSpanIso.hom]
    change (horn₂₀.ι₀₂ ≫ pastingRightSpanFromHorn) ≫ _ = _
    rw [pastingRightSpanFromHorn_right]
    dsimp only [pushoutSpan]
    rw [← Category.assoc horn₂₀.ι₀₂ spanSquareBoundary, spanSquareBoundary_leftEdge]
    apply thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply Subtype.ext <;> apply Subtype.ext <;> apply ULift.ext <;>
      apply Subtype.ext <;> apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories
