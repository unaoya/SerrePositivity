module

public import SerrePositivity.InfinityCategories.F1.CoherentCompositionNestedCut
public import SerrePositivity.InfinityCategories.F1.QCatCorePostcomposition

/-!
概要：第二射を固定した二重切断の始域から終域への Hom を元の後合成で表示する。
方針：第一射の最大座標を最後の零頂点へ戻し、第二射の定値性を使う。
規約：元の第一 Hom の全単体と元の終域輸送射を保持する。
使われ方：第二三角形の長辺に対応する全高次 Hom の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ二重切断の終点への可変 Hom は、第一射の最後の零頂点評価の後の元の後合成。 -/
lemma coherentCompositionNestedCutSimplex_zero_last_fixed
    (A B Z : QCat.{u}) (f : B ⟶ Z) {n : ℕ}
    (σ : (SimplicialCategory.sHom A B) _⦋n⦌)
    (s t : Fin (n + 1) →o Fin 2) (hst : ∀ k, t k = 0 → s k = 0)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : s j = 1) :
    (coherentCompositionNestedCutSimplex σ
      (PinchedHom.constant (SimplicialCategory.homEquiv' B Z f) n) s t).map
        ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentCompositionNestedCutSimplex_obj_zero σ _ s t hst i hi)
        (coherentCompositionNestedCutSimplex_obj_last σ _ s t j hj)) =
      pathCutLastZeroMap t hi j ≫ SSet.yonedaEquiv.symm σ ≫
        quasicategoryCoreMap ((ihom A.obj).map (show B.obj ⟶ Z.obj from f)) := by
  let τ := PinchedHom.constant (SimplicialCategory.homEquiv' B Z f) n
  let D := (SimplicialThickening.functor (coherentPrismCut s).uliftMap).map
    (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
        (coherentPrismCut_zero s i (hst i hi)) (coherentPrismCut_one s j (by rw [hj]; decide)))
  have hD : D ≫ pathCutMaximumMap t hi (Fin.last (n + 1)) = pathCutLastZeroMap t hi j :=
    coherentNestedCut_maximumMap s t hst i j hi (coherentPrismCut_one s j (by rw [hj]; decide))
  calc
    _ = lift (D ≫ pathCutMaximumMap t hi (Fin.last (n + 1)) ≫ SSet.yonedaEquiv.symm σ)
          (D ≫ pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm τ) ≫ eComp SSet A B Z := by
      change (_ ≫ coherentCompositionHom σ τ t (coherentPrismCut s i)
        (coherentPrismCut s j)) ≫ eqToHom _ = _
      rw [Category.assoc, coherentCompositionHom_transport σ τ t
        (coherentPrismCut_zero s i (hst i hi)) (coherentPrismCut_one s j (by rw [hj]; decide))
        (coherentCompositionObj_zero A B Z t i hi) (coherentCompositionObj_last A B Z n t),
        coherentCompositionHom_zero_last σ τ t i hi]
      simp only [← Category.assoc, comp_lift]
      rfl
    _ = lift (pathCutLastZeroMap t hi j ≫ SSet.yonedaEquiv.symm σ)
          (SSet.const (SimplicialCategory.homEquiv' B Z f)) ≫ eComp SSet A B Z := by
      change lift (D ≫ pathCutMaximumMap t hi (Fin.last (n + 1)) ≫ SSet.yonedaEquiv.symm σ)
        (D ≫ pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm
          (PinchedHom.constant (SimplicialCategory.homEquiv' B Z f) n)) ≫ _ = _
      rw [← Category.assoc, hD, yonedaEquiv_symm_pinchedConstant, SSet.comp_const,
        SSet.comp_const]
    _ = _ := by
      rw [← qCatCorePostcomposition_comp]
      simp only [← Category.assoc, comp_lift, Category.comp_id, SSet.comp_const]

end SerrePositivity.InfinityCategories
