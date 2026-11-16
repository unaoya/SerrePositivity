module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Totalization.FiniteTensorComparison
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-!
# 横一行だけの指定積全複体

## 概要
横次数n以外が零の積全複体を、元の第n行の負のnシフトと同定する。

## 方針
指定行射影を鎖写像とし、元の指定成分への挿入を次数ごとの逆に使う。

## 規約
ここで切るのは横次数である。既存の垂直零行の全複体同型とは異なる。

## 使われ方
BS 著者版 Lemma 4.22 の有限頭部の行数に関する帰納。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.HomologicalAlgebra
open SerrePositivity.HomologicalAlgebra.CochainProductTotal

namespace SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
variable {R : Type u} [CommRing R]

/-- 横一行の全微分は、元の縦微分に横次数の符号を掛けたものである。 -/
theorem singleHorizontalRow_d (K : CochainComplex (Complex R) ℕ) (n : ℕ)
    (hK : ∀ m : ℕ, m ≠ n → IsZero (K.X m)) (q : ℤ) :
    (total K).d q (q+1) ≫ componentπ K n (q+1) =
      (n : ℤ).negOnePow • (componentπ K n q ≫ (K.X n).d (q-n) (q+1-n)) := by
  cases n with
  | zero => simpa only [Int.natCast_zero, Int.negOnePow_zero, one_smul] using component_d_zero K q
  | succ n =>
    rw [component_d_succ]
    have hz : K.d n (n+1) = 0 := (hK n (by omega)).eq_zero_of_src _
    simp only [hz, HomologicalComplex.zero_f, comp_zero, zero_comp,
      zero_add]

/-- 他の横行が零なら、指定行射影は各次数で同型となる。 -/
theorem singleHorizontalRow_component_isIso (K : CochainComplex (Complex R) ℕ) (n : ℕ)
    (hK : ∀ m : ℕ, m ≠ n → IsZero (K.X m)) (q : ℤ) :
    IsIso (componentπ K n q) := by
  refine ⟨⟨insertMorphism K q n, ?_, insertMorphism_component_self K q n⟩⟩
  apply component_hom_ext
  intro m
  by_cases hm : m=n
  · subst m
    simp only [Category.assoc, insertMorphism_component_self, Category.comp_id,
      Category.id_comp]
  · exact ((HomologicalComplex.eval (ModuleCat.{u} R) (.up ℤ) (q-m)).map_isZero
      (hK m hm)).eq_of_tgt _ _

/-- 同じ指定行射影から作る、横一行の全複体から元の行のシフトへの鎖写像。 -/
def singleHorizontalRowProjection (K : CochainComplex (Complex R) ℕ) (n : ℕ)
    (hK : ∀ m : ℕ, m ≠ n → IsZero (K.X m)) :
    total K ⟶ (K.X n)⟦-(n : ℤ)⟧ where
  f q := componentπ K n q ≫
    (CochainComplex.shiftFunctorObjXIso (K.X n) (-(n : ℤ)) q (q-n) (by omega)).inv
  comm' i j hij := by
    change i+1=j at hij
    subst j
    rw [← Category.assoc, singleHorizontalRow_d K n hK i, Linear.units_smul_comp]
    simp only [Category.assoc, CochainComplex.shiftFunctor_obj_d',
      CochainComplex.shiftFunctorObjXIso, Linear.comp_units_smul,
      HomologicalComplex.XIsoOfEq_inv_comp_d, HomologicalComplex.d_comp_XIsoOfEq_inv,
      Int.negOnePow_neg]

/-- 横一行の標準射影の鎖同型性。 -/
instance singleHorizontalRowProjection_isIso (K : CochainComplex (Complex R) ℕ) (n : ℕ)
    (hK : ∀ m : ℕ, m ≠ n → IsZero (K.X m)) :
    IsIso (singleHorizontalRowProjection K n hK) := by
  haveI : ∀ q : ℤ, IsIso ((singleHorizontalRowProjection K n hK).f q) := by
    intro q
    haveI := singleHorizontalRow_component_isIso K n hK q
    change IsIso (componentπ K n q ≫ _)
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- 指定した同型は元の行射影である。 -/
def singleHorizontalRowIso (K : CochainComplex (Complex R) ℕ) (n : ℕ)
    (hK : ∀ m : ℕ, m ≠ n → IsZero (K.X m)) : total K ≅ (K.X n)⟦-(n : ℤ)⟧ :=
  asIso (singleHorizontalRowProjection K n hK)

/-- 横一行の指定射影は元の図式の射について自然である。 -/
@[reassoc] theorem singleHorizontalRowProjection_naturality
    {K M : CochainComplex (Complex R) ℕ} (g : K ⟶ M) (n : ℕ)
    (hK : ∀ m : ℕ, m ≠ n → IsZero (K.X m))
    (hM : ∀ m : ℕ, m ≠ n → IsZero (M.X m)) :
    (cochainProductTotalizationFunctor (ModuleCat.{u} R)).map g ≫
        singleHorizontalRowProjection M n hM =
      singleHorizontalRowProjection K n hK ≫ (g.f n)⟦-(n : ℤ)⟧' := by
  apply HomologicalComplex.Hom.ext
  funext q
  simp only [HomologicalComplex.comp_f, singleHorizontalRowProjection,
    CochainComplex.shiftFunctor_map_f', ← Category.assoc, componentπ_naturality]
  simp only [Category.assoc, CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_inv_naturality]

end SerrePositivity.BhattScholze.Prismatic.HTComparisonTotal
