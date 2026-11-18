module

public import SerrePositivity.EInfinity.Modules.TensorAugmentationFamily
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.SimplexCounitContraction
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedTensorAugmentationCurryZero
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedHomZeroRawEvaluation

/-!
# 元の加群 augmentation の転置と同じ恒等閉射

概要：M10 の同じ全 augmentation の転置を単位パラメータの元の恒等閉射へ戻す。
方針：既存の閉射の逆転置則と同じ AW 余単位の零次生成元の値を使う。
規約：HA 1.3.1.13、元の Hom end と同じ全単体同型を保つ。
使われ方：元の augmentation 像と指定恒等辺の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory Opposite MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：元の単位比較の後の閉射を転置すると元の単位パラメータ閉射。
方針：検証済みの同じ逆転置の単射性と閉射の逆転置式を使う。
規約：HA 1.3.1.13、同じ元の射。使われ方：単位余単位の元の照合。 -/
lemma moduleParamCurry_closed {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleParamCurry A D ((moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) M)).hom ≫ f) =
      ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := M) (Y := N) f := by
  apply moduleParamUncurry_injective (M := M) (N := N)
  rw [moduleParamUncurry_curry, moduleParamUncurry_closed]

/-- 概要：同じ左単位比較の転置は元の恒等閉射の単位パラメータ。
方針：元の閉射の式へ同じ恒等射を代入する。
規約：HA 1.3.1.13、同じ恒等射。使われ方：augmentation 転置の指定単位。 -/
lemma moduleParamCurry_unit (P : ModuleCategory A D) :
    moduleParamCurry A D (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) P)).hom =
      ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := P) (Y := P) (𝟙 P) := by
  exact (congrArg (fun f => moduleParamCurry A D (M := P) (N := P) f)
    (Category.comp_id (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) P)).hom)).symm.trans
      (moduleParamCurry_closed A D (𝟙 P))

/-- 概要：元の全 augmentation の転置は同じ AW 余単位の後の元の恒等閉射。
方針：元の係数前合成自然性と単位比較の転置式を合成する。
規約：HA 1.3.1.13、全単体。使われ方：元の零次像の直接評価。 -/
lemma moduleTensorAugmentation_curry (P : ModuleCategory A D) (n : SimplexCategory) :
    moduleParamCurry A D ((moduleTensorSimplicesAugmentation A D P).app n) =
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n) ≫
        ForgetEnrichment.homTo (Complex A) (C := RightModule A D) (X := P) (Y := P) (𝟙 P) := by
  exact (moduleParamCurry_precompose A D
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n))
    (moduleTensorUnitIso A D (ForgetEnrichment.to (Complex A) P)).hom).trans
    (congrArg (fun f => _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n) ≫ f)
      (moduleParamCurry_unit A D P))

/-- 概要：元の零次生成元での augmentation の転置は同じ恒等閉 cochain。
方針：同じ AW 余単位の生成元評価と閉射の単位パラメータを使う。
規約：HA 1.3.1.13、元の閉射。使われ方：実 Γ 像の恒等辺への較正。 -/
lemma moduleTensorAugmentation_curry_zero (P : ModuleCategory A D) :
    (moduleParamCurry A D ((moduleTensorSimplicesAugmentation A D P).app ⦋0⦌)).f 0
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexZeroGenerator A) =
    (closedHomEquiv A (RightModule A D) P P (𝟙 P)).val := by
  rw [moduleTensorAugmentation_curry]
  change (ForgetEnrichment.homTo (Complex A) (𝟙 P)).f 0
    ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj ⦋0⦌)).f 0
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplexZeroGenerator A)) = _
  rw [_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_stdSimplex_eq_contraction]
  exact (congrArg (fun z => (ForgetEnrichment.homTo (Complex A) (𝟙 P)).f 0 z)
    (_root_.SerrePositivity.ComplexLimits.normalizedSimplexCochainAugmentation_zero_generator_eq A)).trans (by rfl)

/-- 概要：元の実 Γ 零次像を同じ単射な直接評価で戻すと元の恒等閉 cochain。
方針：検証済みの正規化 Hom の直接評価と元の転置の生成元評価を合成する。
規約：HA 1.3.1.13、元の Γ・包含・同型。使われ方：同じ標準恒等頂点との照合。 -/
lemma moduleTensorAugmentation_gamma_zero_raw (P : ModuleCategory A D) :
    _root_.SerrePositivity.ComplexLimits.truncationExtendedZeroInclusion A ComplexShape.embeddingDownNat
      _root_.SerrePositivity.ComplexLimits.embeddingDownNat_eq_upIntLE_zero rfl
      (moduleHom A D (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P))
      ((_root_.SerrePositivity.ComplexLimits.gammaDegreeZeroIso ((moduleHom A D (ForgetEnrichment.to (Complex A) P)
        (ForgetEnrichment.to (Complex A) P)).truncLE'
          (ComplexShape.embeddingUpIntLE 0))).hom (moduleTensorAugmentationDoldKanVertex A D P)) =
    (closedHomEquiv A (RightModule A D) P P (𝟙 P)).val :=
  (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_zero_raw A _
    (moduleParamCurry A D ((moduleTensorSimplicesAugmentation A D P).app ⦋0⦌))).trans
      (moduleTensorAugmentation_curry_zero A D P)

end SerrePositivity.EInfinity.Modules
