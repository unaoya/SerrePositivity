module

public import SerrePositivity.KST.Spectra.SpectrumNativeCircleEvaluationTriangle
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：円の評価三角形と参照零三角形を、関手 quasicategory の三次内部ホーンへ貼る。
方針：零射の始点退化を第三面とし、既知の全辺の厳密一致を curry して貼り合わせる。
規約：対象ごとの選択を使わない。使われ方：もう一方の零三角形と loop 四角形の構成。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 参照零三角形を、元の Sp の自己関手の単体集合で読む。 -/
def circleZeroFunctorTriangle : (Δ[2] : SSet.{u + 1}) ⟶ (ihom Sp.{u}).obj Sp.{u} :=
  curry (nativeZeroEvaluationTriangleFamily PointedSimplicialSet.circle)

/-- 円の評価三角形を、元の Sp の自己関手の単体集合で読む。 -/
def circleEvaluationFunctorTriangle : (Δ[2] : SSet.{u + 1}) ⟶ (ihom Sp.{u}).obj Sp.{u} :=
  curry nativeCircleEvaluationTriangleFamily

/-- native cotensor から零関手への辺の、始点を重ねる退化三角形。 -/
def circleZeroDegenerateTriangle : (Δ[2] : SSet.{u + 1}) ⟶ (ihom Sp.{u}).obj Sp.{u} :=
  stdSimplex.σ (0 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) ≫ circleZeroFunctorTriangle

/-- curry による図式の族への移送は、形状の前合成と厳密に可換。 -/
lemma circleFamilyCurry_pre {K L : SSet.{u + 1}} (f : K ⟶ L)
    (T : Sp.{u} ⊗ L ⟶ Sp.{u}) :
    f ≫ curry T = curry ((𝟙 Sp.{u} ⊗ₘ f) ≫ T) :=
  (curry_natural_left f T).symm

/-- 零射の退化三角形の終辺は、参照零三角形の初辺。 -/
lemma circleEvaluationHorn_overlap12 :
    stdSimplex.δ (2 : Fin 3) ≫ circleZeroFunctorTriangle.{u} =
      stdSimplex.δ (0 : Fin 3) ≫ circleZeroDegenerateTriangle := by
  have hs : stdSimplex.δ (0 : Fin 3) ≫ stdSimplex.σ (0 : Fin 2) =
      𝟙 (Δ[1] : SSet.{u + 1}) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [circleZeroDegenerateTriangle, ← Category.assoc, ← Category.assoc, hs, Category.id_comp]

/-- 円の評価三角形の終辺は、参照零三角形の外辺。 -/
lemma circleEvaluationHorn_overlap13 :
    stdSimplex.δ (1 : Fin 3) ≫ circleZeroFunctorTriangle.{u} =
      stdSimplex.δ (0 : Fin 3) ≫ circleEvaluationFunctorTriangle := by
  rw [circleZeroFunctorTriangle, circleEvaluationFunctorTriangle,
    circleFamilyCurry_pre, circleFamilyCurry_pre,
    nativeCircleEvaluationTriangleFamily_target_zero]

/-- 円の評価三角形と零射の退化三角形の初辺は、同じ cotensor の恒等辺。 -/
lemma circleEvaluationHorn_overlap23 :
    stdSimplex.δ (2 : Fin 3) ≫ circleEvaluationFunctorTriangle.{u} =
      stdSimplex.δ (2 : Fin 3) ≫ circleZeroDegenerateTriangle := by
  have hs : (stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.σ (0 : Fin 2)) ≫
      stdSimplex.δ (2 : Fin 3) =
        SSet.const (X := (Δ[1] : SSet.{u + 1}))
          (stdSimplex.obj₀Equiv.symm (0 : Fin 3)) := by
    apply SSet.yonedaEquiv.injective
    decide
  rw [circleZeroDegenerateTriangle, ← Category.assoc, ← Category.assoc, hs,
    circleEvaluationFunctorTriangle, circleZeroFunctorTriangle]
  apply uncurry_injective
  rw [uncurry_natural_left, uncurry_natural_left, uncurry_curry, uncurry_curry]
  change (𝟙 Sp.{u} ⊗ₘ stdSimplex.δ (2 : Fin 3)) ≫
      nativeCircleEvaluationTriangleFamily = _
  rw [nativeCircleEvaluationTriangleFamily_identity]
  change _ = (fst Sp.{u} (Δ[1] : SSet.{u + 1}) ≫
    lift (𝟙 Sp.{u}) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 3)))) ≫ _
  rw [Category.assoc, nativeZeroEvaluationTriangleFamily_zero]

/-- 指定した三面を保持する、元の Sp の関手 quasicategory 内の実際の内部ホーン。 -/
def circleEvaluationHorn : (horn 3 1 : SSet.{u + 1}) ⟶ (ihom Sp.{u}).obj Sp.{u} :=
  horn₃₁.desc circleZeroFunctorTriangle circleEvaluationFunctorTriangle circleZeroDegenerateTriangle
    circleEvaluationHorn_overlap12 circleEvaluationHorn_overlap13 circleEvaluationHorn_overlap23

/-- ホーンの零番目の面は、参照零三角形そのもの。 -/
lemma circleEvaluationHorn_zero :
    horn₃₁.ι₀ ≫ circleEvaluationHorn.{u} = circleZeroFunctorTriangle := horn₃₁.ι₀_desc ..

/-- ホーンの二番目の面は、元の円の評価三角形そのもの。 -/
lemma circleEvaluationHorn_two :
    horn₃₁.ι₂ ≫ circleEvaluationHorn.{u} = circleEvaluationFunctorTriangle := horn₃₁.ι₂_desc ..

/-- ホーンの三番目の面は、零射の退化三角形そのもの。 -/
lemma circleEvaluationHorn_three :
    horn₃₁.ι₃ ≫ circleEvaluationHorn.{u} = circleZeroDegenerateTriangle := horn₃₁.ι₃_desc ..

end SerrePositivity.KST.Spectra.OmegaSpectrum
