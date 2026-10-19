module

public import SerrePositivity.EInfinity.BarrattEccles.AugmentationNaturality
public import SerrePositivity.EInfinity.BarrattEccles.TensorComplexGenerators

/-!
# augmentation の部分合成の保存

概要：Berger–Fresse §1.1 の Barratt–Eccles の augmentation が shuffle 合成を保つことを示す。
方針：終域の0次への集中を使い、二入力の鎖次数がともに0の場合を生成元で計算する。
規約：arity 0 の入力も含め、基礎環の標数を制限しない。
使われ方：可換オペラッドへの augmentation の合成保存の公理を満たす。
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

/-- 概要：0単体の augmentation の値は A[0] の標準の元1である（Berger–Fresse §1.1.2）。
方針：0次の標準同型の逆を用いてスカラーの値の公式を戻す。
規約：終域の元を singleObjXSelf の逆で表す。
使われ方：augmentation を適用したテンソルを単位子で計算する。 -/
lemma complexAugmentation_generator_zero_raw (n : ℕ) (x : (simplicial n) _⦋0⦌) :
    (complexAugmentation A n).f 0
        ((complexXIso A n 0).inv (normalizedGenerator A n 0 x)) =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) := by
  have hu := congrArg (fun f => f ((complexAugmentation A n).f 0
    ((complexXIso A n 0).inv (normalizedGenerator A n 0 x))))
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom_inv_id
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
        ((complexAugmentation A n).f 0
          ((complexXIso A n 0).inv (normalizedGenerator A n 0 x)))) = _ at hu
  rw [complexAugmentation_generator_zero] at hu
  exact hu.symm

/-- 概要：augmentation は全ての部分合成を Com の合成へ送る（Berger–Fresse §1.1.3）。
方針：負の正規化生成元で判定し、正の鎖次数では終域の零性、0次では唯一の shuffle を使う。
規約：Com の合成は A[0] の左単位子である。
使われ方：E から Com へのオペラッド射の comp の公理を与える。 -/
lemma partialComposition_augmentation (m n : ℕ) (i : Fin (m + 1)) :
    partialComposition A m n i ≫ complexAugmentation A (m + n) =
      (complexAugmentation A (m + 1) ⊗ₘ complexAugmentation A n) ≫
        (λ_ (𝟙_ (Complex A))).hom := by
  apply tensor_complex_generator_hom_ext A (m + 1) n
  intro p q x y
  by_cases h : p + q = 0
  · have hp : p = 0 := by omega
    have hq : q = 0 := by omega
    subst p q
    simp only [tensorHom_def, HomologicalComplex.comp_f, ModuleCat.comp_apply]
    erw [SerrePositivity.DifferentialGraded.whiskerRight_apply
      (complexAugmentation A (m + 1)) (complex A n) 0 0 0 rfl]
    erw [SerrePositivity.DifferentialGraded.whiskerLeft_apply
      (𝟙_ (Complex A)) (complexAugmentation A n) 0 0 0 rfl]
    rw [partialComposition_neg_tmul A m n i 0 0]
    simp only [Iso.inv_hom_id_apply]
    rw [shuffleBilinear_generators,
      complexAugmentation_generator_zero_raw A (m + 1) x,
      complexAugmentation_generator_zero_raw A n y]
    erw [← cochain_leftUnitor_inv_apply A (𝟙_ (Complex A)) 0
      ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))]
    have hr : (λ_ (𝟙_ (Complex A))).hom.f 0
        ((λ_ (𝟙_ (Complex A))).inv.f 0
          ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) =
        (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) :=
      congrArg (fun f => f.f 0 ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)))
        (λ_ (𝟙_ (Complex A))).inv_hom_id
    erw [hr]
    let _ : Unique (ShufflePath 0 0) := {
      default := zeroLeftPath 0
      uniq := fun s => s.leftZero_unique (zeroLeftPath 0) }
    simp only [shuffleValue, Fintype.sum_unique, ShufflePath.sign_leftZero, Units.val_one, one_smul]
    erw [complexAugmentation_generator_zero_raw A (m + n)]
  · have hz := isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A))
      (-((p + q : ℕ) : ℤ)) (by omega)
    let _ := ModuleCat.isZero_iff_subsingleton.mp hz
    exact Subsingleton.elim _ _

end SerrePositivity.EInfinity.BarrattEccles
