module

public import SerrePositivity.KST.Spectra.IntervalSquareSweeps

/-!
概要：元の正方形の下辺・左辺から対角へのホモトピーと、その両端の式。
方針：座標の最小値による変形を元の正方形へ後合成する。
規約：新しい充填を選ばない。使われ方：元の円評価 loop と companion の両端固定比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.IntervalSquare

/-- 下辺変形の経路始点は、正方形の元の左下頂点に固定される。 -/
lemma bottomSweep_source :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        bottomSweep = SSet.const
          (Y := (Δ[1] : SSet.{u}) ⊗ Δ[1])
          (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) := by
  rw [bottomSweep, comp_lift, lift_fst, meet_source]
  rfl

/-- 下辺変形の経路終点は、元の右辺を走る。 -/
lemma bottomSweep_target :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        bottomSweep =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) := by
  rw [bottomSweep, comp_lift, lift_fst, meet_target]

/-- 左辺変形の経路始点も、正方形の元の左下頂点に固定される。 -/
lemma leftSweep_source :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        leftSweep = SSet.const
          (Y := (Δ[1] : SSet.{u}) ⊗ Δ[1])
          (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0) := by
  rw [leftSweep, comp_lift, meet_source, lift_fst]
  rfl

/-- 左辺変形の経路終点は、元の上辺を走る。 -/
lemma leftSweep_target :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        leftSweep =
      lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) := by
  rw [leftSweep, comp_lift, meet_target, lift_fst]

variable {Y : SSet.{u}}

/-- 元の正方形を保つ、下辺から対角への実際のホモトピー。 -/
def bottomHomotopy (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Y) :
    SSet.Homotopy
      (lift (𝟙 (Δ[1] : SSet.{u}))
        (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) ≫ Q)
      (lift (𝟙 (Δ[1] : SSet.{u})) (𝟙 _) ≫ Q) where
  h := bottomSweep ≫ Q
  h₀ := by
    rw [← Category.assoc, bottomSweep_zero]
    rfl
  h₁ := by
    rw [← Category.assoc, bottomSweep_one]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    exact False.elim a.property

/-- 元の正方形を保つ、左辺から同じ対角への実際のホモトピー。 -/
def leftHomotopy (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Y) :
    SSet.Homotopy
      (lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
        (𝟙 (Δ[1] : SSet.{u})) ≫ Q)
      (lift (𝟙 (Δ[1] : SSet.{u})) (𝟙 _) ≫ Q) where
  h := leftSweep ≫ Q
  h₀ := by
    rw [← Category.assoc, leftSweep_zero]
    rfl
  h₁ := by
    rw [← Category.assoc, leftSweep_one]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    rintro ⟨a, t⟩
    exact False.elim a.property

/-- 下辺ホモトピーの始点は、元の左下頂点で定値。 -/
lemma bottomHomotopy_source (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Y) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        (bottomHomotopy Q).h =
      SSet.const (Q.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)) := by
  change _ ≫ (bottomSweep ≫ Q) = _
  rw [← Category.assoc, bottomSweep_source, SSet.const_comp]

/-- 下辺ホモトピーの終点は、元の右辺そのもの。 -/
lemma bottomHomotopy_target (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Y) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        (bottomHomotopy Q).h =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
        (𝟙 (Δ[1] : SSet.{u})) ≫ Q := by
  change _ ≫ (bottomSweep ≫ Q) = _
  rw [← Category.assoc, bottomSweep_target]

/-- 左辺ホモトピーの始点も、元の左下頂点で定値。 -/
lemma leftHomotopy_source (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Y) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        (leftHomotopy Q).h =
      SSet.const (Q.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 0)) := by
  change _ ≫ (leftSweep ≫ Q) = _
  rw [← Category.assoc, leftSweep_source, SSet.const_comp]

/-- 左辺ホモトピーの終点は、元の上辺そのもの。 -/
lemma leftHomotopy_target (Q : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Y) :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        (leftHomotopy Q).h =
      lift (𝟙 (Δ[1] : SSet.{u}))
        (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ≫ Q := by
  change _ ≫ (leftSweep ≫ Q) = _
  rw [← Category.assoc, leftSweep_target]

end SerrePositivity.KST.Spectra.IntervalSquare
