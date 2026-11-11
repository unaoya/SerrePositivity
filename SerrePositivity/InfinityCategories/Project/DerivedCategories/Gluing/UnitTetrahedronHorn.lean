module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.NormalizationTetrahedronFilling
/-! # 単位四面体の三指定面と退化四面体の同じ内角

概要：二つの終側面が一致し、前側面が単位退化する四面体を同じ退化四面体と内角上で照合する。
方針：有限の面・退化等式で Λ[3,2] の三面を比較する。
規約：選択済み四面体を変更せず、未供給の相対比較の存在は仮定しない。
使われ方：F1B の相対内角比較を残る左単位面へ適用する入口を供給する。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
lemma dgGluingUnitTetrahedron_zero_degeneracy :
    stdSimplex.δ (0 : Fin 4) ≫ stdSimplex.σ (0 : Fin 3) = 𝟙 (Δ[2] : SSet.{u}) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro j
  fin_cases j <;> rfl
lemma dgGluingUnitTetrahedron_one_degeneracy :
    stdSimplex.δ (1 : Fin 4) ≫ stdSimplex.σ (0 : Fin 3) = 𝟙 (Δ[2] : SSet.{u}) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro j
  fin_cases j <;> rfl
lemma dgGluingUnitTetrahedron_three_degeneracy :
    stdSimplex.δ (3 : Fin 4) ≫ stdSimplex.σ (0 : Fin 3) =
      (stdSimplex.σ (0 : Fin 2) : (Δ[2] : SSet.{u}) ⟶ Δ[1]) ≫
        stdSimplex.δ (2 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro j
  fin_cases j <;> rfl
lemma dgGluingUnitTetrahedron_two_degeneracy :
    stdSimplex.δ (2 : Fin 4) ≫ stdSimplex.σ (0 : Fin 3) =
      (stdSimplex.σ (0 : Fin 2) : (Δ[2] : SSet.{u}) ⟶ Δ[1]) ≫
        stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  apply SSet.stdSimplex.ext
  intro j
  fin_cases j <;> rfl

lemma dgGluingUnitTetrahedron_horn_eq {Z : SSet.{u}}
    (T : (Δ[3] : SSet.{u}) ⟶ Z) (U : (Δ[2] : SSet.{u}) ⟶ Z)
    (h0 : stdSimplex.δ (0 : Fin 4) ≫ T = U)
    (h1 : stdSimplex.δ (1 : Fin 4) ≫ T = U)
    (h3 : stdSimplex.δ (3 : Fin 4) ≫ T =
      stdSimplex.σ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) ≫ U) :
    (horn 3 2).ι ≫ T = (horn 3 2).ι ≫ stdSimplex.σ (0 : Fin 3) ≫ U := by
  apply horn.hom_ext'
  intro j hj
  fin_cases j
  · simp only [← Category.assoc, horn.ι_ι]
    change stdSimplex.δ (0 : Fin 4) ≫ T =
      (stdSimplex.δ (0 : Fin 4) ≫ stdSimplex.σ (0 : Fin 3)) ≫ U
    rw [h0, dgGluingUnitTetrahedron_zero_degeneracy, Category.id_comp]
  · simp only [← Category.assoc, horn.ι_ι]
    change stdSimplex.δ (1 : Fin 4) ≫ T =
      (stdSimplex.δ (1 : Fin 4) ≫ stdSimplex.σ (0 : Fin 3)) ≫ U
    rw [h1, dgGluingUnitTetrahedron_one_degeneracy, Category.id_comp]
  · exact (hj rfl).elim
  · simp only [← Category.assoc, horn.ι_ι]
    change stdSimplex.δ (3 : Fin 4) ≫ T =
      (stdSimplex.δ (3 : Fin 4) ≫ stdSimplex.σ (0 : Fin 3)) ≫ U
    rw [h3, dgGluingUnitTetrahedron_three_degeneracy, Category.assoc]
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
