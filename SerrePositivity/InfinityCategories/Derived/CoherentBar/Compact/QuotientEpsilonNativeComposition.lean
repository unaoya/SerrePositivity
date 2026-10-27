module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonHorizontalFunctor
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonNative

/-!
概要：固定 ε 整合商作用の横合成保存を native core 上の全単体で供給する。
方針：実 dg 横合成の等号と native tensor 比較の全単体自然性を合成する。
規約：対象・零単体の等号だけで結論しない。
使われ方：D-S の厳密豊穣入力作用の商への延長。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (C D E : Type v)
  [DGCategory R C] [DGCategory R D] [DGCategory R E]
  [Small.{u} C] [Small.{u} D] [Small.{u} E]
  (S : Set C) (T : Set D) (U : Set E)

/-- ε 整合関手の native core 上の実横合成。 -/
def quotientEpsilonNativeComposition :
    quotientEpsilonNativeSpace R C D S T ⊗ quotientEpsilonNativeSpace R D E T U ⟶
      quotientEpsilonNativeSpace R C E S U :=
  dgNerveCoreTensor R (NullPreservingFunctorsε R C D S T)
    (NullPreservingFunctorsε R D E T U) ≫
      quasicategoryCoreMap (dgNerve.map (quotientEpsilonHorizontalFunctor R C D E S T U))

/-- 商作用は native Hom の横合成を全単体で厳密に保つ。 -/
lemma quotientEpsilonNativeMap_composition :
    quotientEpsilonNativeComposition R C D E S T U ≫ quotientEpsilonNativeMap R C E S U =
      (quotientEpsilonNativeMap R C D S T ⊗ₘ quotientEpsilonNativeMap R D E T U) ≫
        dgFunctorNativeComposition R (DGQuotient.QuotientObject C S)
          (DGQuotient.QuotientObject D T) (DGQuotient.QuotientObject E U) := by
  let H := quotientEpsilonHorizontalFunctor R C D E S T U
  let Q := quotientInputFunctor R C E S U
  have h := congrArg (fun F => quasicategoryCoreMap (dgNerve.map F))
    (quotientEpsilonHorizontalFunctor_quotient R C D E S T U)
  simp only [dgNerve.map_comp] at h
  change quasicategoryCoreFunctor.map _ = quasicategoryCoreFunctor.map _ at h
  simp only [Functor.map_comp] at h
  dsimp only [quasicategoryCoreFunctor] at h
  change (dgNerveCoreTensor R _ _ ≫ quasicategoryCoreMap (dgNerve.map H)) ≫
    quasicategoryCoreMap (dgNerve.map Q) = _
  rw [Category.assoc, h]
  have ht : (quotientInputFunctor R C D S T).tensor (quotientInputFunctor R D E T U) =
      dgTensorFunctor R (quotientInputFunctor R C D S T) (quotientInputFunctor R D E T U) := rfl
  rw [ht, ← Category.assoc, ← dgNerveCoreTensor_naturality]
  rfl

end SerrePositivity.InfinityCategories
