module

public import SerrePositivity.HomologicalAlgebra.SimplicialChains.Shuffle.AlexanderWhitneySums
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric

/-!
# shuffle 成分と AW 余積の可換性

概要：Berger–Fresse §1.1.4 の AW 余代数射性を次数ごとの加群射の等式にする。
方針：正規化生成元の純テンソル上で、前後の shuffle 和への分解公式を使う。
規約：中間二因子を交換する Koszul 符号を明示する。
使われ方：shuffle を鎖写像へ束ねた後の余代数射性の検証。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.SimplicialChains.Shuffle

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped _root_.Simplicial _root_.TensorProduct

variable (A : Type u) [CommRing A]

/-- 概要：shuffle 成分は AW 余積を Koszul 符号つきで保つ（BF §1.1.4）。
方針：正規化生成元の純テンソルで射の外延性を使い、対角の有限和公式へ帰着する。
規約：r,t は二つの入力の独立な切断座標。
使われ方：一般 shuffle 鎖写像と E の部分合成の余代数適合性。 -/
lemma component_diagonal (X Y : SSet.{0}) (p q : ℕ) :
    _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y p q ≫ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.diagonal A (X ⊗ Y)).f (p + q) =
      ∑ r : Fin (p + 1), ∑ t : Fin (q + 1),
        (-1 : ℤ) ^ (t.val * (p - r.val)) •
          ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A X p r.val (p - r.val) (by omega) ⊗ₘ
              _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component A Y q t.val (q - t.val) (by omega)) ≫
            tensorμ ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X r.val)
              ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A X).X (p - r.val))
              ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).X t.val)
              ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A Y).X (q - t.val)) ≫
            (_root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y r.val t.val ⊗ₘ _root_.SerrePositivity.SimplicialChains.Shuffle.component A X Y (p - r.val) (q - t.val)) ≫
            ιTensorObj (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y))
              (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.chains A (X ⊗ Y)) (r.val + t.val)
              ((p - r.val) + (q - t.val)) (p + q) (by omega)) := by
  apply _root_.SerrePositivity.SimplicialChains.Shuffle.tensor_generator_hom_ext A X Y p q
  intro x y
  simp only [ModuleCat.comp_apply, _root_.SerrePositivity.SimplicialChains.Shuffle.component_generators, ModuleCat.hom_sum,
    LinearMap.sum_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply,
    ModuleCat.MonoidalCategory.tensorHom_tmul, _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.component_generator,
    ModuleCat.MonoidalCategory.tensorμ_apply, _root_.SerrePositivity.SimplicialChains.Shuffle.component_generators]
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.diagonal_value]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro t _
  erw [ModuleCat.MonoidalCategory.tensorHom_tmul]
  rw [_root_.SerrePositivity.SimplicialChains.Shuffle.component_generators, _root_.SerrePositivity.SimplicialChains.Shuffle.component_generators]

end SerrePositivity.SimplicialChains.Shuffle
