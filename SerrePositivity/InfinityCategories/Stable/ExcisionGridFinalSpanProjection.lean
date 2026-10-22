module
public import SerrePositivity.InfinityCategories.Stable.ExcisionGridFinalSquare

/-!
概要：最終面の同じ二辺と実余錐の射影の厳密比較。
方針：同じ実図式の native 余錐・頂点・二辺を保持して比較する。
規約：一般安定性を先取りしない。使われ方：HA 1.4.2.15 の外側の面。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {P Q : Type u} [PartialOrder P] [PartialOrder Q]

lemma excisionGridFinalSpanShapeIso_projection :
    excisionGridFinalSpanShapeIso.{u}.hom ≫
      (fullSubcomplexOnVertices (nerve ExcisionGridFullPastIndex.{u})
        (fun v ↦ IsExcisionGridFinalSpan (nerveEquiv v))).ι ≫
      nerveMap (posetSubtypeInclusion IsExcisionGridFullPast) =
        pushoutSpan excisionGridFinalSquare := by
  dsimp only [excisionGridFinalSpanShapeIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc]
  apply horn₂₀.isPushout.hom_ext
  · rw [← Category.assoc horn₂₀.ι₀₁ pastingRightSpanIso.hom]
    change (horn₂₀.ι₀₁ ≫ pastingRightSpanFromHorn) ≫ _ = _
    rw [pastingRightSpanFromHorn_left]
    dsimp only [pushoutSpan]
    rw [← Category.assoc horn₂₀.ι₀₁ spanSquareBoundary, spanSquareBoundary_bottomEdge]
    apply thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply ULift.ext <;> apply Subtype.ext <;>
      apply Prod.ext <;> apply Fin.ext <;> decide
  · rw [← Category.assoc horn₂₀.ι₀₂ pastingRightSpanIso.hom]
    change (horn₂₀.ι₀₂ ≫ pastingRightSpanFromHorn) ≫ _ = _
    rw [pastingRightSpanFromHorn_right]
    dsimp only [pushoutSpan]
    rw [← Category.assoc horn₂₀.ι₀₂ spanSquareBoundary, spanSquareBoundary_leftEdge]
    apply thinNerveHom_ext_of_vertices
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    fin_cases i <;> apply ULift.ext <;> apply Subtype.ext <;>
      apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories
