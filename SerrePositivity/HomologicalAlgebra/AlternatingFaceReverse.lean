module
public import SerrePositivity.HomologicalAlgebra.AlternatingReverseSigns
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.AlgebraicTopology.SimplicialObject.Op
public import Mathlib.CategoryTheory.Linear.Basic
import all Mathlib.AlgebraicTopology.AlternatingFaceMapComplex

/-!
概要：単体的対象の順序反転を、交代面複体の明示的な符号同型で元へ戻す。
方針：n+1 次元の境界の符号を計算し、次数ごとの符号を漸化式で選ぶ。
規約：各次数の係数は整数の単元。反転の同型を恒等射と取り違えない。
使われ方：HA 1.2.4、G10 の反対 under nerve と BK over nerve の線形比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology Opposite
open scoped Simplicial
namespace SerrePositivity.HomologicalAlgebra
variable {C : Type*} [Category* C] [Preadditive C]

/-- 単体順序反転の交代境界は元の境界の (-1)^(n+1) 倍。 -/
theorem alternatingFaceReverse_boundary (W : SimplicialObject C) (n : ℕ) :
    AlternatingFaceMapComplex.objD (SimplicialObject.opFunctor.obj W) n =
      (-1 : ℤ) ^ (n+1) • AlternatingFaceMapComplex.objD W n := by
  simpa [AlternatingFaceMapComplex.objD, SimplicialObject.opFunctor,
    SimplicialObject.δ] using alternating_sum_rev n (fun i => W.δ i)

/-- 反転の次数符号。零次数は 1、次の次数では境界の反転符号を掛ける。 -/
def alternatingFaceReverseSign : ℕ → ℤˣ
  | 0 => 1
  | n+1 => ((n+1 : ℕ) : ℤ).negOnePow * alternatingFaceReverseSign n

/-- 単体順序反転を同じ次数の符号付き恒等射で元へ戻す同型。 -/
def alternatingFaceReverseDegreeIso (W : SimplicialObject C) (n : ℕ) :
    (AlternatingFaceMapComplex.obj (SimplicialObject.opFunctor.obj W)).X n ≅
      (AlternatingFaceMapComplex.obj W).X n where
  hom := alternatingFaceReverseSign n • 𝟙 _
  inv := (alternatingFaceReverseSign n)⁻¹ • 𝟙 _
  hom_inv_id := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, Category.id_comp,
      smul_smul, mul_inv_cancel, one_smul]
    rfl
  inv_hom_id := by
    rw [Linear.units_smul_comp, Linear.comp_units_smul, Category.id_comp,
      smul_smul, inv_mul_cancel, one_smul]
    rfl

/-- 順序反転した単体的対象の交代面複体を、元の複体へ戻す指定符号同型。 -/
def alternatingFaceReverseIso (W : SimplicialObject C) :
    AlternatingFaceMapComplex.obj (SimplicialObject.opFunctor.obj W) ≅
      AlternatingFaceMapComplex.obj W :=
  HomologicalComplex.Hom.isoOfComponents (alternatingFaceReverseDegreeIso W) (by
    intro n m hnm
    have hn : m+1=n := hnm
    subst n
    simp only [AlternatingFaceMapComplex.obj_d_eq]
    change (alternatingFaceReverseSign (m+1) • 𝟙 _) ≫ AlternatingFaceMapComplex.objD W m =
      AlternatingFaceMapComplex.objD (SimplicialObject.opFunctor.obj W) m ≫
        (alternatingFaceReverseSign m • 𝟙 _)
    erw [alternatingFaceReverse_boundary, Linear.units_smul_comp, Category.id_comp,
      Linear.comp_units_smul, Category.comp_id]
    rw [alternatingFaceReverseSign, mul_smul]
    simpa only [Units.smul_def, Int.coe_negOnePow_natCast] using
      (smul_comm (((m+1 : ℕ) : ℤ).negOnePow) (alternatingFaceReverseSign m)
        (AlternatingFaceMapComplex.objD W m)))

/-- 順序反転の鎖同型は単体的対象の全射に自然。 -/
def alternatingFaceReverseNatIso :
    SimplicialObject.opFunctor (C := C) ⋙ alternatingFaceMapComplex C ≅
      alternatingFaceMapComplex C :=
  NatIso.ofComponents alternatingFaceReverseIso (by
    intro W V f
    apply HomologicalComplex.Hom.ext
    funext n
    change f.app (op ⦋n⦌) ≫ (alternatingFaceReverseSign n • 𝟙 _) =
      (alternatingFaceReverseSign n • 𝟙 _) ≫ f.app (op ⦋n⦌)
    erw [Linear.comp_units_smul, Category.comp_id,
      Linear.units_smul_comp, Category.id_comp])

/-- 零次数では反転の鎖同型は恒等射であり、元の頂点評価を保つ。 -/
theorem alternatingFaceReverseIso_hom_f_zero (W : SimplicialObject C) :
    (alternatingFaceReverseIso W).hom.f 0 = 𝟙 _ := by
  change (1 : ℤˣ) • 𝟙 _ = _
  exact one_smul _ _

end SerrePositivity.HomologicalAlgebra
