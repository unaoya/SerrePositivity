module

public import SerrePositivity.InfinityCategories.F1.CoherentNestedCutFixedPostcomposition

/-!
概要：第二射を固定した二重切断の中間対象から終域への Hom は元の第二射に定値。
方針：合成単体の後半の Hom を定値第二パラメーターで計算する。
規約：元の終域輸送射を変更しない。
使われ方：第二三角形の終域側の全高次 Hom の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 同じ二重切断の中間対象から終域への Hom は、元の固定第二射に定値。 -/
lemma coherentCompositionNestedCutSimplex_middle_last_fixed
    (A B Z : QCat.{u}) (f : B ⟶ Z) {n : ℕ}
    (σ : (SimplicialCategory.sHom A B) _⦋n⦌)
    (s t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hsi : s i = 0) (hi : t i = 1) (hj : s j = 1) :
    (coherentCompositionNestedCutSimplex σ
      (PinchedHom.constant (SimplicialCategory.homEquiv' B Z f) n) s t).map
        ⟨ULift.up i⟩ ⟨ULift.up j⟩ ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (coherentCompositionNestedCutSimplex_obj_middle σ _ s t i hsi hi)
        (coherentCompositionNestedCutSimplex_obj_last σ _ s t j hj)) =
      SSet.const (SimplicialCategory.homEquiv' B Z f) := by
  let τ := PinchedHom.constant (SimplicialCategory.homEquiv' B Z f) n
  change (_ ≫ coherentCompositionHom σ τ t (coherentPrismCut s i)
    (coherentPrismCut s j)) ≫ eqToHom _ = _
  rw [Category.assoc, coherentCompositionHom_transport σ τ t
    (coherentPrismCut_zero s i hsi) (coherentPrismCut_one s j (by rw [hj]; decide))
    (coherentCompositionObj_one A B Z t i (by rw [hi]; decide))
    (coherentCompositionObj_last A B Z n t),
    coherentCompositionHom_one_last σ τ t i (by rw [hi]; decide)]
  rw [show SSet.yonedaEquiv.symm τ = SSet.const (SimplicialCategory.homEquiv' B Z f) from
    yonedaEquiv_symm_pinchedConstant _ _]
  simp only [SSet.comp_const]

end SerrePositivity.InfinityCategories
