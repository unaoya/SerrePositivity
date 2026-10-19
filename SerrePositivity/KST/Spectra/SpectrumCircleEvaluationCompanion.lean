module

public import SerrePositivity.KST.Spectra.SpectrumCircleEvaluationHorn

/-!
概要：関手 quasicategory の内部ホーンを充填し、円の生成辺を保持するもう一方の零三角形。
方針：三つの指定面を保持する三単体を選び、欠けた面とその対角を計算する。
規約：元の Sp 全体で一つの coherent な選択。使われ方：二つの零三角形の四角形への貼合。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 指定した三面を保つ、元の Sp の自己関手の quasicategory 内の三単体。 -/
def circleEvaluationTetrahedron : (Δ[3] : SSet.{u + 1}) ⟶ (ihom Sp.{u}).obj Sp.{u} :=
  (Quasicategory.hornFilling (by decide) (by decide) circleEvaluationHorn).choose

/-- 選んだ三単体は、元の指定ホーン全体を厳密に保持する。 -/
lemma circleEvaluationTetrahedron_restrict :
    (horn 3 1).ι ≫ circleEvaluationTetrahedron.{u} = circleEvaluationHorn :=
  (Quasicategory.hornFilling (by decide) (by decide) circleEvaluationHorn).choose_spec.symm

/-- 三単体の零番目の面は参照零三角形。 -/
lemma circleEvaluationTetrahedron_zero :
    stdSimplex.δ (0 : Fin 4) ≫ circleEvaluationTetrahedron.{u} = circleZeroFunctorTriangle := by
  rw [← horn.ι_ι (1 : Fin 4) 0 (by decide), Category.assoc,
    circleEvaluationTetrahedron_restrict]
  exact circleEvaluationHorn_zero

/-- 三単体の二番目の面は元の円の評価三角形。 -/
lemma circleEvaluationTetrahedron_two :
    stdSimplex.δ (2 : Fin 4) ≫ circleEvaluationTetrahedron.{u} =
      circleEvaluationFunctorTriangle := by
  rw [← horn.ι_ι (1 : Fin 4) 2 (by decide), Category.assoc,
    circleEvaluationTetrahedron_restrict]
  exact circleEvaluationHorn_two

/-- 三単体の三番目の面は元の零射の退化三角形。 -/
lemma circleEvaluationTetrahedron_three :
    stdSimplex.δ (3 : Fin 4) ≫ circleEvaluationTetrahedron.{u} = circleZeroDegenerateTriangle := by
  rw [← horn.ι_ι (1 : Fin 4) 3 (by decide), Category.assoc,
    circleEvaluationTetrahedron_restrict]
  exact circleEvaluationHorn_three

/-- 円の生成辺と三つの指定面を保持して構成した、もう一方の零三角形。 -/
def circleZeroCompanionTriangle : (Δ[2] : SSet.{u + 1}) ⟶ (ihom Sp.{u}).obj Sp.{u} :=
  stdSimplex.δ (1 : Fin 4) ≫ circleEvaluationTetrahedron

/-- もう一方の零三角形と参照零三角形は、同じ対角の辺を持つ。 -/
lemma circleZeroCompanionTriangle_diagonal :
    stdSimplex.δ (1 : Fin 3) ≫ circleZeroCompanionTriangle.{u} =
      stdSimplex.δ (1 : Fin 3) ≫ circleZeroFunctorTriangle := by
  have hs : (stdSimplex.δ (1 : Fin 3) : (Δ[1] : SSet.{u + 1}) ⟶ Δ[2]) ≫
      stdSimplex.δ (1 : Fin 4) =
      stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (2 : Fin 4) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [circleZeroCompanionTriangle, ← Category.assoc, hs, Category.assoc,
    circleEvaluationTetrahedron_two, circleEvaluationFunctorTriangle, circleZeroFunctorTriangle,
    circleFamilyCurry_pre, circleFamilyCurry_pre,
    nativeCircleEvaluationTriangleFamily_source_zero]

/-- もう一方の零三角形の初辺は、参照零三角形の初辺を保持する。 -/
lemma circleZeroCompanionTriangle_initial :
    stdSimplex.δ (2 : Fin 3) ≫ circleZeroCompanionTriangle.{u} =
      stdSimplex.δ (2 : Fin 3) ≫ circleZeroFunctorTriangle := by
  have hs : (stdSimplex.δ (2 : Fin 3) : (Δ[1] : SSet.{u + 1}) ⟶ Δ[2]) ≫
      stdSimplex.δ (1 : Fin 4) = stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4) := by
    apply SSet.yonedaEquiv.injective
    decide
  have hd : stdSimplex.δ (1 : Fin 3) ≫ stdSimplex.σ (0 : Fin 2) =
      𝟙 (Δ[1] : SSet.{u + 1}) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [circleZeroCompanionTriangle, ← Category.assoc, hs, Category.assoc,
    circleEvaluationTetrahedron_three, circleZeroDegenerateTriangle,
    ← Category.assoc, ← Category.assoc, hd, Category.id_comp]

/-- もう一方の零三角形の終辺も、参照零三角形の終辺を保持する。 -/
lemma circleZeroCompanionTriangle_final :
    stdSimplex.δ (0 : Fin 3) ≫ circleZeroCompanionTriangle.{u} =
      stdSimplex.δ (0 : Fin 3) ≫ circleZeroFunctorTriangle := by
  have hs : (stdSimplex.δ (0 : Fin 3) : (Δ[1] : SSet.{u + 1}) ⟶ Δ[2]) ≫
      stdSimplex.δ (1 : Fin 4) = stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.δ (0 : Fin 4) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [circleZeroCompanionTriangle, ← Category.assoc, hs, Category.assoc,
    circleEvaluationTetrahedron_zero]

end SerrePositivity.KST.Spectra.OmegaSpectrum
