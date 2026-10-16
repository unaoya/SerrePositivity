module
public import SerrePositivity.DifferentialGraded.Quotient.Paths
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-! # 収縮記号を消す次数+1 cochain

ε複体の次数−1生成元を単位複体の次数0生成元へ送る。
これは内部Hom微分について閉じた次数+1 cochainであり、閉零chain mapではない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A]

/-- dε=idに使う、εを単位へ送る次数+1の線形cochain。 -/
def eraseEpsilon : Cochain (epsilonComplex A) (𝟙_ (Complex A)) 1 :=
  Cochain.fromSingleMk (p := -1) (q := 0) (n := 1)
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (by omega)

/-- ε消去cochainは内部Hom微分について閉じている。 -/
lemma eraseEpsilon_closed : δ 1 2 (eraseEpsilon A) = 0 := by
  rw [eraseEpsilon, Cochain.δ_fromSingleMk _ _ 2 1 (by omega)]
  change Cochain.fromSingleMk
    ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv ≫
      ((single (ModuleCat.{u} A) (.up ℤ) 0).obj (𝟙_ (ModuleCat.{u} A))).d 0 1)
    (show (-1 : ℤ) + 2 = 1 by omega) = 0
  simp only [single_obj_d, comp_zero, Cochain.fromSingleMk_zero]

/-- 唯一の非零成分は次数−1から0へ単位Aをそのまま送る。 -/
lemma eraseEpsilon_v :
    (eraseEpsilon A).v (-1) 0 (by omega) =
      (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).hom ≫
        (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv :=
  Cochain.fromSingleMk_v _ _

/-- 次数−1の標準生成元の像は次数0の標準生成元。 -/
lemma eraseEpsilon_generator :
    (eraseEpsilon A).v (-1) 0 (by omega)
      ((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) =
        (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv (1 : A) := by
  rw [eraseEpsilon_v]
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} A))).inv
    (((singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).inv ≫
      (singleObjXSelf (.up ℤ) (-1) (𝟙_ (ModuleCat.{u} A))).hom) (1 : A)) = _
  rw [Iso.inv_hom_id]
  rfl

end SerrePositivity.DifferentialGraded.DGQuotient
