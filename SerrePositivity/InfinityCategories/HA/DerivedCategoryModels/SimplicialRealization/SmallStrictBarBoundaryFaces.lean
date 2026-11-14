module

public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarBoundarySum
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarBlockCoefficients
import all SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization.SmallStrictBarTotalValues
import all SerrePositivity.InfinityCategories.Project.DerivedCategories.KanModels.CoherentBar.Faces.DGCoherentBarFaces

/-!
# 交代面境界の同じ先頭を保つ項

## 概要
先頭を保つ面の項は、同じ面のシフト前の標準列になる。

## 方針
先頭の射が恒等射であることを用い、元の余積包含を保つ。

## 規約
元の面のラベルと cochain の次数を保持する。

## 使われ方
HA 1.2.4。coherent bar の面の列と交代面境界の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open HomologicalComplex CochainComplex HomComplex SerrePositivity.DifferentialGraded
open scoped _root_.Simplicial
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
open SerrePositivity.HomologicalAlgebra
open SerrePositivity.InfinityCategories.Project.DerivedCategories
variable (A : Type u) [CommRing A] {J : Type} [SmallCategory J]

private theorem cochainHExt {K L : Complex A} {a b : ℤ} (z : Cochain K L a)
    (w : Cochain K L b) (h : a = b)
    (hv : ∀ p q (hp : p + a = q) (hq : p + b = q), z.v p q hp = w.v p q hq) : HEq z w := by
  subst b
  apply heq_of_eq
  apply Cochain.ext
  intro p q hpq
  exact hv p q hpq hpq

/-- 先頭を保つ面の境界項は、元の同じ面のシフト前の列。 -/
theorem smallStrictBarBoundaryTerm_succ (F : J ⥤ ModuleCategory A PUnit.{1}) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) (i : Fin (n + 1)) :
    HEq (smallStrictBarBoundaryTerm A F n s i.succ)
      (smallStrictBarUnshiftedColumn A F (dgCoherentBarFace s i.succ)) := by
  apply cochainHExt A _ _ (by
    change -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ)
    omega)
  intro p q hp hq
  dsimp only [dgCoherentBarFace] at hq ⊢
  have hpn : p + -(n : ℤ) = q := by omega
  unfold smallStrictBarBoundaryTerm smallStrictBarUnshiftedColumn
  dsimp only [Prod.fst, Prod.snd]
  apply (Cochain.comp_v _ _ _ p p q (by omega) hpn).trans
  have hf : s.down.map (homOfLE (Fin.zero_le ((SimplexCategory.δ i.succ).toOrderHom 0))) =
      𝟙 (s.down.obj 0) := by
    exact s.down.map_id 0
  erw [hf, CategoryTheory.Functor.map_id, Category.id_comp]
  exact (smallStrictBarUnshiftedColumn_v A F (dgCoherentBarFace s i.succ) p q hq).symm

/-- 最初の tail は元の第零面と同じ添字である。 -/
theorem smallStrictBarTail_eq_face_zero (n : ℕ)
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) :
    dgCoherentBarTail s 1 (by omega) = dgCoherentBarFace s 0 := by
  have h : SimplexCategory.mkHom (dgCoherentBarTailOrder (n + 1) 1 (by omega)) =
      SimplexCategory.δ (0 : Fin (n + 2)) := by
    ext j
    simp [dgCoherentBarTailOrder, SimplexCategory.δ, Fin.succAbove, SimplexCategory.mkHom]
    omega
  unfold dgCoherentBarTail dgCoherentBarFace
  rw [h]
  rfl

/-- 第零面の境界項は、元の先頭の射の後の同じ面の列。 -/
theorem smallStrictBarBoundaryTerm_zero (F : J ⥤ ModuleCategory A PUnit.{1}) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) :
    HEq (smallStrictBarBoundaryTerm A F n s 0)
      ((Cochain.ofHom ((smallStrictBarCoefficientDiagram A F).map
        (s.down.map (homOfLE (Fin.zero_le (Fin.succ (0 : Fin (n + 1)))))))).comp
        (smallStrictBarUnshiftedColumn A F (dgCoherentBarFace s 0)) (zero_add _)) := by
  apply cochainHExt A _ _ (by
    change -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ)
    omega)
  intro p q hp hq
  have hpn : p + -(n : ℤ) = q := by omega
  unfold smallStrictBarBoundaryTerm
  apply (Cochain.comp_v _ _ _ p p q (by omega) hpn).trans
  symm
  apply (Cochain.comp_v _ _ _ p p q (by omega) hpn).trans
  erw [smallStrictBarUnshiftedColumn_v A F (dgCoherentBarFace s 0) p q hq]
  simp only [Cochain.ofHom_v, HomologicalComplex.comp_f, Category.assoc]
  rfl

/-- 次数の異種等号で一致する列は、同じ次数へシフトした後に一致する。 -/
theorem unsignedLeftShift_of_heq {K L : Complex A} {a b : ℤ}
    (z : Cochain K L a) (w : Cochain K L b) (h : HEq z w)
    (m r : ℤ) (hr : a + m = r) (hs : b + m = r) :
    unsignedLeftShift z m r hr = unsignedLeftShift w m r hs := by
  have hab : a = b := by omega
  subst b
  cases eq_of_heq h
  rfl

private theorem dependentColumnCongr {α : Sort _} {β : α → Sort _}
    (f : ∀ a, β a) {a b : α} (h : a = b) : HEq (f a) (f b) := by
  cases h
  rfl

/-- 第零面の同じ境界列を、元の最初の prefix としてシフトした等式。 -/
theorem smallStrictBarBoundaryTerm_zero_shift (F : J ⥤ ModuleCategory A PUnit.{1}) (n : ℕ)
    (s : ((SSet.uliftFunctor.{u, 0}).obj (nerve J)) _⦋n + 1⦌) :
    unsignedLeftShift (smallStrictBarBoundaryTerm A F n s 0) ((n + 1 : ℕ) : ℤ) 1 (by omega) =
      unsignedLeftShift
        ((Cochain.ofHom ((smallStrictBarCoefficientDiagram A F).map
          (s.down.map (homOfLE (Fin.zero_le (Fin.succ (0 : Fin (n + 1)))))))).comp
          (smallStrictBarUnshiftedColumn A F (dgCoherentBarTail s 1 (by omega))) (zero_add _))
        ((n + 1 : ℕ) : ℤ) 1 (by
          change -(n : ℤ) + ((n + 1 : ℕ) : ℤ) = 1
          omega) := by
  apply (unsignedLeftShift_of_heq A _ _ (smallStrictBarBoundaryTerm_zero A F n s) _ _ _ _).trans
  have hz₀ : HEq (smallStrictBarUnshiftedColumn A F (dgCoherentBarTail s 1 (by omega)))
      (smallStrictBarUnshiftedColumn A F (dgCoherentBarFace s 0)) :=
    dependentColumnCongr (smallStrictBarUnshiftedColumn A F)
      (a := dgCoherentBarTail s 1 (by omega)) (b := dgCoherentBarFace s 0)
      (smallStrictBarTail_eq_face_zero n s)
  have hz := eq_of_heq hz₀
  exact congrArg (fun z : Cochain
    ((smallStrictBarCoefficientDiagram A F).obj (s.down.obj (Fin.succ 0)))
    ((smallStrictBarTotalTarget A F).obj (op PUnit.unit)) (-(n : ℤ)) =>
      unsignedLeftShift ((Cochain.ofHom ((smallStrictBarCoefficientDiagram A F).map
        (s.down.map (homOfLE (Fin.zero_le (Fin.succ (0 : Fin (n + 1)))))))).comp z (zero_add _))
        ((n + 1 : ℕ) : ℤ) 1 (by omega)) hz.symm

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
