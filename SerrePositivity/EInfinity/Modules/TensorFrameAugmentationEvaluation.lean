module
public import SerrePositivity.EInfinity.Modules.TensorFrameEvaluation

/-!
概要：同じ符号付き frame 同型を通した元の加群 augmentation の評価を計算する。
方針：AW 余単位の実評価式と交換同型・単位子の法則を使う。
規約：HA 1.3.1.13、Berger–Fresse §1.1.4、元の余単位を保持。
使われ方：M10 の元の全屋根の augmentation 側の係数移送。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 概要：同じ frame 同型の後の augmentation 評価は元の AW 余単位の右テンソル。
方針：符号付き交換の自然性と単位における交換の式を貼り合わせる。
規約：HA 1.3.1.13、元の実射。使われ方：全要素屋根の左脚の比較。 -/
lemma moduleTensorEvaluationFrameIso_augmentation (P : ModuleCategory A D) (x : D)
    (n : SimplexCategory) :
    (moduleTensorEvaluationFrameIso A D P x).hom.app n ≫
      (moduleEvaluation A D x).map ((moduleTensorSimplicesAugmentation A D P).app n) =
    (𝟙 ((moduleEvaluation A D x).obj P) ⊗ₘ
      AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n)) ≫
        (ρ_ ((moduleEvaluation A D x).obj P)).hom := by
  rw [moduleTensorSimplicesAugmentation_eval]
  change (signedSwap _ _).hom ≫ (_ ≫ _) = _
  rw [← Category.assoc, ← signedSwap_naturality]
  rw [Category.assoc]
  change _ ≫ ((β_ ((moduleEvaluation A D x).obj P) (𝟙_ (Complex A))).hom ≫
    (λ_ ((moduleEvaluation A D x).obj P)).hom) = _
  rw [CategoryTheory.braiding_leftUnitor]

end SerrePositivity.EInfinity.Modules
