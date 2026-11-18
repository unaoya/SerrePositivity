module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionEvaluation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSeparationTripleSwap

/-!
模型。文献の定義との比較は後で
# テンソル冪の二列への分離

概要：Berger–Fresse §3.1 の反復評価に使う、対のテンソル冪を二列へ分ける同型を作る。
方針：tensorμ を先頭から反復し、先頭二因子の交換と両立することを示す。
規約：零重テンソルの分離は単位子の逆射。
使われ方：反復評価の等変性を通常のテンソル冪の自然性へ帰着する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：対の n 重テンソルを二列の n 重テンソルへ分離する（BF §3.1）。
方針：尾を分離してから tensorμ で先頭の二因子を各列へ合わせる。
規約：Koszul 符号は既存の tensorμ に含む。
使われ方：反復評価と対称群の作用を比較する。 -/
def tensorPowerSeparation (V W : Complex A) : ∀ n : ℕ,
    power (V ⊗ W) n ≅ power V n ⊗ power W n
  | 0 => (λ_ (𝟙_ (Complex A))).symm
  | n + 1 => whiskerLeftIso (V ⊗ W) (tensorPowerSeparation V W n) ≪≫
      { hom := tensorμ V W (power V n) (power W n)
        inv := tensorδ V W (power V n) (power W n)
        hom_inv_id := tensorμ_tensorδ _ _ _ _
        inv_hom_id := tensorδ_tensorμ _ _ _ _ }

/-- 概要：二列への分離は先頭二対の交換と可換（BF §3.1）。
方針：尾の分離を交換の前へ移し、三対の分離と交換の整合性を適用する。
規約：交換後も列内の尾の順序は保つ。
使われ方：任意の隣接交換に関する帰納法の基底となる。 -/
lemma tensorPowerSeparation_firstSwap (V W : Complex A) (n : ℕ) :
    (swapFirstIso (V ⊗ W) n).hom ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (n + 2)).hom =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (n + 2)).hom ≫
      ((swapFirstIso V n).hom ⊗ₘ (swapFirstIso W n).hom) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso_naturality (𝟙 (V ⊗ W)) (𝟙 (V ⊗ W))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom
  simp only [id_tensorHom] at hn
  change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso (V ⊗ W) (V ⊗ W) (power (V ⊗ W) n)).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (n + 2)).hom = _
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation, Iso.trans_hom, whiskerLeftIso_hom,
    whiskerLeft_comp, Category.assoc]
  rw [← reassoc_of% hn]
  exact congrArg (fun f => ((V ⊗ W) ◁ ((V ⊗ W) ◁
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W n).hom)) ≫ f)
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso_separation V W V W (power V n) (power W n))

/-- 概要：二列への分離は全ての隣接交換と可換（BF §3.1）。
方針：先頭交換を基底とし、尾の交換へ帰納して tensorμ の自然性を使う。
規約：同じ位置を二列で同時に交換する。
使われ方：全置換と分離の両立を対称群の生成性で証明する。 -/
lemma tensorPowerSeparation_adjacent (V W : Complex A) (n : ℕ) (i : Fin n) :
    (adjacentIso (V ⊗ W) n i).hom ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (n + 1)).hom =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (n + 1)).hom ≫
      ((adjacentIso V n i).hom ⊗ₘ (adjacentIso W n i).hom) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation_firstSwap V W n
    · change ((V ⊗ W) ◁ (adjacentIso (V ⊗ W) n j).hom) ≫
        ((V ⊗ W) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (n + 1)).hom) ≫
        tensorμ V W (power V (n + 1)) (power W (n + 1)) =
        (((V ⊗ W) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W (n + 1)).hom) ≫
          tensorμ V W (power V (n + 1)) (power W (n + 1))) ≫
        ((V ◁ (adjacentIso V n j).hom) ⊗ₘ (W ◁ (adjacentIso W n j).hom))
      rw [← whiskerLeft_comp_assoc, ih j]
      simp only [whiskerLeft_comp, Category.assoc]
      rw [tensorμ_natural_right]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
