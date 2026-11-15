module
public import SerrePositivity.EInfinity.Modules.NormalizedAugmentationComparison
public import SerrePositivity.EInfinity.Modules.TensorFrameAugmentationEvaluation
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedSimplexTensorAugmentation

/-!
概要：同じ frame 評価同型を通して、元の二つの指定 augmentation を厳密に結ぶ。
方針：AW 余単位と指定収縮の順射の一致を全テンソル係数に送る。
規約：HA 1.3.1.13、元の二本の実射。
使われ方：M10 の複体側の指定三角形の全評価による再利用。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.ComplexLimits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：同じ全 frame 同型は元の二つの augmentation と可換。
方針：AW 余単位の実評価と元の収縮の実順射の等式を合成する。
規約：HA 1.3.1.13、全次元。使われ方：指定全屋根の左脚の比較。 -/
lemma moduleTensorEvaluationFrameIso_original_augmentation (P : ModuleCategory A D) (x : D)
    (n : SimplexCategory) :
    (moduleTensorEvaluationFrameIso A D P x).hom.app n ≫
      (moduleEvaluation A D x).map ((moduleTensorSimplicesAugmentation A D P).app n) =
    (normalizedSimplexTensorAugmentation A ((moduleEvaluation A D x).obj P)).app n :=
  (moduleTensorEvaluationFrameIso_augmentation A D P x n).trans
    (congrArg (fun z => (𝟙 ((moduleEvaluation A D x).obj P) ⊗ₘ z) ≫
      (ρ_ ((moduleEvaluation A D x).obj P)).hom)
      (normalizedSimplexCochainContraction_hom_counit A n).symm)

end SerrePositivity.EInfinity.Modules
