module

public import Mathlib.RepresentationTheory.Homological.FiniteCyclic
public import Mathlib.Algebra.CharP.Lemmas

/-!
# P⁰ のための両側周期的な係数複体

DAG XIII Construction 2.2.6 の Tate 経路に使う鎖レベルの部品。
偶数次数の微分は ρ(g) − 1、奇数次数はノルムとし、整数全体で定義する。
有限巡回群の生成元を指定したときの完全解像度の係数複体に対応する。
このファイルではスペクトル的な Tate 構成との比較をまだ主張しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
variable {k : Type u} [CommRing k] {G : Type v} [CommGroup G] [Fintype G]

/-- 両側周期的な係数微分。 -/
def cyclicTateDifferential (A : Rep k G) (g : G) (i : ℤ) : A ⟶ A :=
  if Even i then A.applyAsHom g - 𝟙 A else A.norm.asHom

lemma cyclicTateDifferential_sq (A : Rep k G) (g : G) (i : ℤ) :
    cyclicTateDifferential A g i ≫ cyclicTateDifferential A g (i + 1) = 0 := by
  by_cases hi : Even i
  · have hn : ¬Even (i + 1) := Int.not_even_iff_odd.mpr hi.add_one
    simp only [cyclicTateDifferential, ite_eq_left hi, ite_eq_right hn]
    ext
    simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm]
  · have hn : Even (i + 1) := (Int.not_even_iff_odd.mp hi).add_one
    simp only [cyclicTateDifferential, ite_eq_right hi, ite_eq_left hn]
    ext
    simp [Rep.sub_hom, Rep.applyAsHom, Rep.norm]

/-- 微分の全表現射に関する自然性。 -/
lemma cyclicTateDifferential_natural {A B : Rep k G} (f : A ⟶ B) (g : G) (i : ℤ) :
    cyclicTateDifferential A g i ≫ f = f ≫ cyclicTateDifferential B g i := by
  by_cases hi : Even i
  · simp only [cyclicTateDifferential, ite_eq_left hi, Preadditive.sub_comp,
      Preadditive.comp_sub, Category.id_comp, Category.comp_id]
    rw [Rep.applyAsHom_comm]
  · simpa only [cyclicTateDifferential, ite_eq_right hi] using (Rep.norm_comm f).symm

/-- 整数全次数にわたる、ノルムと作用差による係数複体。 -/
def cyclicTateComplex (A : Rep k G) (g : G) : CochainComplex (Rep k G) ℤ :=
  CochainComplex.of (fun _ => A) (cyclicTateDifferential A g)
    (cyclicTateDifferential_sq A g)

/-- 同じ微分を用いる係数複体の全関手。 -/
def cyclicTateComplexFunctor (g : G) : Rep k G ⥤ CochainComplex (Rep k G) ℤ where
  obj A := cyclicTateComplex A g
  map f := {
    f _ := f
    comm' i j := by
      dsimp [cyclicTateComplex, CochainComplex.of.d]
      split_ifs with h
      · subst j
        simpa using (cyclicTateDifferential_natural f g i).symm
      · simp }
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- 自明な作用と標数に一致する群の位数では、同じ指定微分が零。 -/
lemma cyclicTateDifferential_trivial (A : Rep k G) [A.IsTrivial]
    (p : ℕ) [CharP k p] (hp : Fintype.card G = p) (g : G) (i : ℤ) :
    cyclicTateDifferential A g i = 0 := by
  by_cases hi : Even i
  · simp only [cyclicTateDifferential, ite_eq_left hi]
    ext x
    simp [Rep.sub_hom, Representation.isTrivial_apply]
  · simp only [cyclicTateDifferential, ite_eq_right hi]
    ext x
    simp [Rep.norm, Representation.norm, Representation.isTrivial_def, hp,
      ← Nat.cast_smul_eq_nsmul k]

end SerrePositivity.EInfinity.PowerOperation
