module

public import SerrePositivity.EInfinity.BarrattEccles.AugmentationCochainValues
public import SerrePositivity.EInfinity.BarrattEccles.NormalizedRightAction
public import SerrePositivity.EInfinity.BarrattEccles.OperadStructure
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Commutative

/-!
# augmentation の対称列の自然性と単位保存

概要：Berger–Fresse §1.1 の EΣₙ の一点への写像を対称列の augmentation にまとめる。
方針：終域が0次に集中することと0次生成元の値1を使う。
規約：対称群作用は augmentation の終域では自明である。
使われ方：可換オペラッドへの射の自然変換と単位保存則を与える。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：E(n) の0次からの加群射は0単体の生成元で決まる（Berger–Fresse §1.1.2）。
方針：正規化鎖の標準同型を前合成し、生成元での射の外延性を使う。
規約：出力は任意の A 加群でよい。
使われ方：augmentation の自然性と保存則を0単体で検証する。 -/
lemma complex_zero_generator_hom_ext (n : ℕ) {M : ModuleCat.{u} A}
    (f g : (complex A n).X 0 ⟶ M)
    (h : ∀ x : (simplicial n) _⦋0⦌,
      f ((complexXIso A n 0).inv (normalizedGenerator A n 0 x)) =
        g ((complexXIso A n 0).inv (normalizedGenerator A n 0 x))) : f = g := by
  apply (cancel_epi (complexXIso A n 0).inv).1
  apply normalizedGenerator_hom_ext A n 0
  exact h

/-- 概要：augmentation は対称群の右作用を消す（Berger–Fresse §1.1）。
方針：0次生成元の像が置換によらず1であることを使う。
規約：終域の A[0] には自明な作用を入れる。
使われ方：対称列としての augmentation の自然性を与える。 -/
lemma complexRightAction_augmentation (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    complexRightAction A n σ ≫ complexAugmentation A n = complexAugmentation A n := by
  apply to_single_hom_ext
  apply (cancel_mono (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom).1
  apply complex_zero_generator_hom_ext A n
  intro x
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((complexAugmentation A n).f 0 ((complexRightAction A n σ).f 0
        ((complexXIso A n 0).inv (normalizedGenerator A n 0 x)))) =
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((complexAugmentation A n).f 0 ((complexXIso A n 0).inv (normalizedGenerator A n 0 x)))
  erw [complexRightAction_normalized_inv_apply A n 0 σ]
  rw [normalizedChainMap_generator, complexAugmentation_generator_zero,
    complexAugmentation_generator_zero]

/-- 概要：E(n) から A[0] への augmentation の対称列の自然変換（Berger–Fresse §1.1）。
方針：各 arity の収縮の順方向の射を用い、右作用との両立性を適用する。
規約：終域は Com の定数対称列である。
使われ方：可換オペラッドへの射の底の自然変換となる。 -/
def augmentationSequence : (sequence A) ⟶ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.commutativeOperad A).sequence where
  app X := complexAugmentation A (FiniteBijection.card X)
  naturality {X Y} f := by
    obtain rfl := FiniteBijection.object_eq_of_hom f
    change (normalizedFunctor A).map (simplicialSequenceMap f) ≫
        complexAugmentation A (FiniteBijection.card X) =
      complexAugmentation A (FiniteBijection.card X) ≫ 𝟙 _
    rw [Category.comp_id, simplicialSequenceMap_self]
    exact complexRightAction_augmentation A _ _

/-- 概要：augmentation は Barratt–Eccles の単位を Com の単位へ送る（Berger–Fresse §1.1.3）。
方針：単位の0次の値と0単体の augmentation の値1を使う。
規約：終域の単位は A[0] の恒等射である。
使われ方：オペラッド射の単位保存の公理を満たす。 -/
lemma unit_augmentation : unit A ≫ complexAugmentation A 1 = 𝟙 (𝟙_ (Complex A)) := by
  apply to_single_hom_ext
  apply (cancel_mono (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom).1
  apply (cancel_epi (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((complexAugmentation A 1).f 0
        ((unit A).f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)))) = _
  rw [unit_zero_apply, one_smul, complexAugmentation_generator_zero]
  exact (congrArg (fun f => f (1 : A))
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv_hom_id).symm

end SerrePositivity.EInfinity.BarrattEccles
