module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.CellUnitNonzero
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.KST.SConstruction.DGFunctorHomElements

/-!
概要：零対象を持つ入力から、標準 cell 分解への dg 関手は存在しない。
方針：dg 関手の鎖線形性と単位保存を、分解先の厳密単位の非零性に照合する。
規約：dg 関手圏間の dg 持ち上げに対する反例。native SSet 射の非存在は主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory DifferentialGraded KST.SConstruction
open scoped ZeroObject
open DGCategoryCellResolution
variable (R : Type u) [CommRing R] [Nontrivial R]
  (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 鎖として単位が零の対象を、非零単位しか持たない cell 分解へは送れない。 -/
lemma dgFunctor_toCellResolution_impossible {C : Type w} [DGCategory R C]
    (x : C) (hx : (unitElement R x).val = 0)
    (F : DGFunctor R C (Source R D)) : False := by
  have h := F.map_unitElement R x
  rw [hx, map_zero] at h
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgCellResolution_unit_ne_zero R D (F.obj x) h.symm

/-- 反例に用いる、一対象かつ全 Hom が零の dg 圏。 -/
inductive CellZeroInput : Type z
  | point

instance cellZeroInputSubsingleton : Subsingleton CellZeroInput.{z} :=
  ⟨by intro x y; cases x; cases y; rfl⟩

instance cellZeroInputDGCategory : DGCategory R CellZeroInput.{z} where
  Hom _ _ := 0
  id _ := 0
  comp _ _ _ := 0
  id_comp _ _ := by simp
  comp_id _ _ := by simp
  assoc _ _ _ _ := by simp

lemma cellZeroInput_unit :
    (unitElement R (CellZeroInput.point : CellZeroInput.{z})).val = 0 := rfl

/-- 反例の入力関手圏でも単位変換は零である。 -/
lemma cellZeroInputFunctor_unit (F : DGFunctor R CellZeroInput.{z} CellZeroInput.{z}) :
    (unitElement R F).val = 0 := by
  have hi : dgFunctorIdentity R CellZeroInput.{z} CellZeroInput.{z} F = 0 := by
    apply dgFunctorHom_ext
    intro x
    rw [dgFunctorIdentity_π, Limits.zero_comp]
    rfl
  change (cycleFromUnit _ (dgFunctorIdentity R CellZeroInput.{z} CellZeroInput.{z} F)).val = 0
  rw [hi]
  rfl

/-- 零入力の関手圏からは、任意の非空の源を持つ cell 値関手圏へも dg 作用はない。 -/
theorem no_dgZeroInputFamily (E : Type w) [DGCategory R E] [Small.{u} E] (x : E) :
    ¬ Nonempty (DGFunctor R (DGFunctor R CellZeroInput.{z} CellZeroInput.{z})
      (DGFunctor R E (Source R D))) := by
  rintro ⟨P⟩
  exact dgFunctor_toCellResolution_impossible R D
    (DGFunctor.id CellZeroInput.{z}) (cellZeroInputFunctor_unit R _)
    (P.comp (dgFunctorEvaluationDG R E (Source R D) x))

/-- 一般の comparisonFunctor 族を dg 関手圏間の dg 関手へ強化することは不可能。 -/
theorem no_dgCellComparisonInputFunctor :
    ¬ Nonempty (DGFunctor R (DGFunctor R CellZeroInput.{z} CellZeroInput.{z})
      (DGFunctor R (Source R CellZeroInput.{z}) (Source R CellZeroInput.{z}))) := by
  rintro ⟨P⟩
  let E := dgFunctorEvaluationDG R (Source R CellZeroInput.{z})
    (Source R CellZeroInput.{z}) ⟨CellZeroInput.point⟩
  exact dgFunctor_toCellResolution_impossible R CellZeroInput.{z}
    (DGFunctor.id CellZeroInput.{z}) (cellZeroInputFunctor_unit R _ ) (P.comp E)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
