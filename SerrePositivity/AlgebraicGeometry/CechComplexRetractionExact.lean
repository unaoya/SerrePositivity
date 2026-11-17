module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
概要：同じ複体のretractの単位則から、各次数の完全性を戻す。
方針：元のhomologyの射の合成則と零対象の判定を使う。
規約：係数環と加群の宇宙を分け、層の導来関手との比較は行わない。
使われ方：元のsingleを増大項とする全複体へ完全性を戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type v} [CommRing R]

/-- 同じ複体のretractは、元の各次数の完全性を保つ。 -/
theorem cechComplex_acyclic_of_retraction
    {C D : CochainComplex (ModuleCat.{u} R) ℕ} (i : C ⟶ D) (r : D ⟶ C)
    (hir : i ≫ r = 𝟙 C) (hD : D.Acyclic) : C.Acyclic := by
  intro n
  rw [HomologicalComplex.exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  have he := congrArg (fun f : C ⟶ C ↦ HomologicalComplex.homologyMap f n) hir
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id] at he
  have hz := (hD n).isZero_homology.eq_zero_of_tgt (HomologicalComplex.homologyMap i n)
  rw [hz, CategoryTheory.Limits.zero_comp] at he
  exact he.symm

end SerrePositivity.AlgebraicGeometry
