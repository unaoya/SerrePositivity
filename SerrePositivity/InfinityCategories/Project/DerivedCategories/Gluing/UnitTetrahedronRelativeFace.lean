module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.UnitTetrahedronHorn
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.RelativeHomotopyRestriction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomotopyRetargetValue
/-! # 相対単位四面体比較から三辺固定の左単位面比較を得る

概要：Λ[3,2] を固定する四面体比較を、残る第2面の三辺固定比較へ制限する。
方針：残る面の各辺を既知の三つの内角面へ因子分解する。
規約：供給待ちの相対比較だけを明示入力に隔離し、元四面体と全入力を保持する。
使われ方：左単位対角閉路の零性を六片の高次貼り合わせへ供給する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

def dgGluingUnitMissingFaceIndex (i : Fin 3) : Fin 4 := ![0, 1, 3] i
def dgGluingUnitMissingEdgeIndex (i : Fin 3) : Fin 3 := ![1, 1, 2] i
lemma dgGluingUnitMissingFaceIndex_ne (i : Fin 3) : dgGluingUnitMissingFaceIndex i ≠ 2 := by
  fin_cases i <;> decide
lemma dgGluingUnitMissingFace_edge (i : Fin 3) :
    stdSimplex.δ i ≫ stdSimplex.δ (2 : Fin 4) =
      (stdSimplex.δ (dgGluingUnitMissingEdgeIndex i) : (Δ[1] : SSet.{u}) ⟶ Δ[2]) ≫
        stdSimplex.δ (dgGluingUnitMissingFaceIndex i) := by
  fin_cases i
  all_goals apply SSet.yonedaEquiv.injective
  all_goals apply SSet.stdSimplex.ext
  all_goals intro j
  all_goals fin_cases j <;> rfl

variable {K Z : SSet.{u}} (T : (Δ[3] : SSet.{u}) ⊗ K ⟶ Z)
  (U : (Δ[2] : SSet.{u}) ⊗ K ⟶ Z)
lemma dgGluingUnitMissingFace_degenerate_family :
    (stdSimplex.δ (2 : Fin 4) ▷ K) ≫ (stdSimplex.σ (0 : Fin 3) ▷ K) ≫ U =
      (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ U := by
  rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingUnitTetrahedron_two_degeneracy,
    comp_whiskerRight, Category.assoc]

variable (H : SSet.Homotopy T ((stdSimplex.σ (0 : Fin 3) ▷ K) ≫ U))
  (hH : (((horn 3 2).ι ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
    fst ((horn 3 2 : SSet.{u}) ⊗ K) Δ[1] ≫ ((horn 3 2).ι ▷ K) ≫
      (stdSimplex.σ (0 : Fin 3) ▷ K) ≫ U)

def dgGluingUnitMissingFaceRelativeHomotopy :
    SSet.Homotopy ((stdSimplex.δ (2 : Fin 4) ▷ K) ≫ T)
      ((stdSimplex.σ (0 : Fin 2) ▷ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ U) :=
  _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (stdSimplex.δ (2 : Fin 4) ▷ K)) rfl
    (dgGluingUnitMissingFace_degenerate_family U)

lemma dgGluingUnitMissingFaceRelativeHomotopy_h :
    (dgGluingUnitMissingFaceRelativeHomotopy T U H).h =
      ((stdSimplex.δ (2 : Fin 4) ▷ K) ▷ (Δ[1] : SSet.{u})) ≫ H.h := rfl

include hH in
lemma dgGluingUnitMissingFaceRelativeHomotopy_fixed (i : Fin 3) :
    ((stdSimplex.δ i ▷ K) ▷ (Δ[1] : SSet.{u})) ≫
        (dgGluingUnitMissingFaceRelativeHomotopy T U H).h =
      fst (Δ[1] ⊗ K) Δ[1] ≫ (stdSimplex.δ i ▷ K) ≫
        (stdSimplex.σ (0 : Fin 2) ▷ K) ≫ (stdSimplex.δ (1 : Fin 3) ▷ K) ≫ U := by
  let a := (stdSimplex.δ (dgGluingUnitMissingEdgeIndex i) ▷ K) ≫
    (horn.ι (2 : Fin 4) (dgGluingUnitMissingFaceIndex i)
      (dgGluingUnitMissingFaceIndex_ne i) ▷ K)
  have he : (stdSimplex.δ i ▷ K) ≫ (stdSimplex.δ (2 : Fin 4) ▷ K) =
      a ≫ ((horn 3 2).ι ▷ K) := by
    simp only [a, ← comp_whiskerRight, Category.assoc, horn.ι_ι,
      dgGluingUnitMissingFace_edge]
  have h := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingRelativeHomotopy_restrict_fixed H ((horn 3 2).ι ▷ K) hH
    (stdSimplex.δ (2 : Fin 4) ▷ K) (stdSimplex.δ i ▷ K) a he
  rw [dgGluingUnitMissingFaceRelativeHomotopy_h]
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp, Category.assoc,
    dgGluingUnitMissingFace_degenerate_family U] using h
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
