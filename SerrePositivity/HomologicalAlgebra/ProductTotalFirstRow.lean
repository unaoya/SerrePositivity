module
public import SerrePositivity.HomologicalAlgebra.ProductTotalZeroRow
public import Mathlib.Algebra.Homology.Homotopy
import all Mathlib.Algebra.Homology.TotalComplex

/-!
概要：積全複体の零行射影に横微分を合成した射の指定零ホモトピー。
方針：第一行への次数 -1 の射影を使い、全微分の二項公式を読む。
規約：縦次数は非有界。元の射影を保持し、任意のホモトピーの選択はしない。
使われ方：HA 1.2.4、G10 の二つの余面と標準脚の両立。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u
open CategoryTheory CategoryTheory.Preadditive Opposite HomologicalComplex
open scoped SerrePositivity.HomologicalAlgebra.ProductTotal
namespace SerrePositivity.HomologicalAlgebra.ProductTotal
variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [∀ K : HomologicalComplex₂ Cᵒᵖ (.down ℤ) (.down ℤ), K.HasTotal (.down ℤ)]

/-- 次数が合わないとき零とする、同じ積全複体の成分射影。 -/
def πOrZero (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ)) (a b q : ℤ) :
    ((functor C).obj K).X q ⟶ (K.X a).X b :=
  (((doubleOpFunctor C).obj (op K)).ιTotalOrZero (.down ℤ) a b q).unop

/-- 次数が合う場合は元の指定射影。 -/
theorem πOrZero_eq (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (a b q : ℤ) (h : a+b=q) : πOrZero K a b q = π K a b q h :=
  congrArg Quiver.Hom.unop
    (((doubleOpFunctor C).obj (op K)).ιTotalOrZero_eq (.down ℤ) a b q h)

/-- 次数が合わない場合は零。 -/
theorem πOrZero_eq_zero (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (a b q : ℤ) (h : a+b≠q) : πOrZero K a b q = 0 := by
  exact congrArg Quiver.Hom.unop
    (((doubleOpFunctor C).obj (op K)).ιTotalOrZero_eq_zero (.down ℤ) a b q h)

/-- 第一行の射影による、零行からの横微分の指定零ホモトピー。 -/
def firstRowHomotopy (K : HomologicalComplex₂ C (.up ℤ) (.up ℤ))
    (hK : K.d (-1) 0 = 0) : Homotopy (zeroRowHom K hK ≫ K.d 0 1) 0 where
  hom i j := πOrZero K 1 j i
  zero i j hij := by
    apply πOrZero_eq_zero
    change ¬ (j+1=i) at hij
    omega
  comm i := by
    have hd := d_π K 1 i i (by omega)
    have hd' : ((functor C).obj K).d i (i+1) ≫ πOrZero K 1 i (i+1) =
        π K 0 i i (by omega) ≫ (K.d 0 1).f i -
          πOrZero K 1 (i-1) i ≫ (K.X 1).d (i-1) i := by
      rw [πOrZero_eq K 1 i (i+1) (by omega),
        πOrZero_eq K 1 (i-1) i (by omega)]
      change _ = π K 0 i i _ ≫ (K.d 0 1).f i +
        (-1 : ℤˣ) • (π K 1 (i-1) i _ ≫ (K.X 1).d (i-1) i) at hd
      simpa [Units.smul_def, sub_eq_add_neg] using hd
    rw [dNext_eq _ (by simp : (ComplexShape.up ℤ).Rel i (i+1)),
      prevD_eq _ (by simp : (ComplexShape.up ℤ).Rel (i-1) i)]
    change π K 0 i i _ ≫ (K.d 0 1).f i =
      ((functor C).obj K).d i (i+1) ≫ πOrZero K 1 i (i+1) +
        πOrZero K 1 (i-1) i ≫ (K.X 1).d (i-1) i + 0
    rw [hd']
    abel

end SerrePositivity.HomologicalAlgebra.ProductTotal
