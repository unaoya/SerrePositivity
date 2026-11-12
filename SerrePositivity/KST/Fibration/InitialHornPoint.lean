module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinFunctor

/-! # 初期一ホーンと元の零単体の厳密な同型 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Fibration

/-- 初期一ホーンは元の区間の始点の面そのもの。 -/
lemma initialHorn_eq_face : horn.{u} 1 0 = stdSimplex.face {0} := by
  have hc : ({(1 : Fin 2)}ᶜ : Finset (Fin 2)) = {0} := by decide
  apply le_antisymm
  · rw [horn_eq_iSup, iSup_le_iff]
    rintro ⟨j, hj⟩
    fin_cases j
    · simp at hj
    · change stdSimplex.face.{u} ({(1 : Fin 2)}ᶜ) ≤ _
      rw [hc]
  · simpa only [hc] using (face_le_horn.{u} (1 : Fin 2) 0 (by decide))

/-- 元の零単体から初期一ホーンへの、全次数の単体を保つ同型。 -/
def initialHornPointIso : (Δ[0] : SSet.{u}) ≅ (Λ[1, 0] : SSet.{u}) :=
  stdSimplex.faceSingletonIso (0 : Fin 2) ≪≫ Subcomplex.eqToIso initialHorn_eq_face.symm

/-- この同型の区間への包含は、元の始点の面射。 -/
lemma initialHornPointIso_ι : initialHornPointIso.{u}.hom ≫ (horn 1 0).ι =
    stdSimplex.δ (1 : Fin 2) := by
  change ((stdSimplex.faceSingletonIso (0 : Fin 2)).hom ≫
    (Subcomplex.eqToIso initialHorn_eq_face.symm).hom) ≫ _ = _
  rw [Category.assoc]
  have he : (Subcomplex.eqToIso initialHorn_eq_face.symm).hom ≫ (horn.{u} 1 0).ι =
      (stdSimplex.face {0}).ι := rfl
  rw [he]
  exact stdSimplex.faceSingletonIso_zero_hom_comp_ι_eq_δ

end SerrePositivity.KST.Fibration
