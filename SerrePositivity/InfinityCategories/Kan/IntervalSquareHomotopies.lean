module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kan.IntervalSquareSweeps

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
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.IntervalSquare
end SerrePositivity.KST.Spectra.IntervalSquare
namespace SerrePositivity.InfinityCategories.Kan.IntervalSquare
open SerrePositivity.KST.Spectra.IntervalSquare

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

end SerrePositivity.InfinityCategories.Kan.IntervalSquare

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.bottomHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.bottomHomotopy := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.bottomHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.bottomHomotopy_source := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.bottomHomotopy_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.bottomHomotopy_target := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.bottomHomotopy_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.bottomSweep_source := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.bottomSweep_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.bottomSweep_target := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.bottomSweep_target

@[deprecated _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.leftHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.leftHomotopy := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.leftHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.leftHomotopy_source := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.leftHomotopy_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.leftHomotopy_target := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.leftHomotopy_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.leftSweep_source := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.leftSweep_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.leftSweep_target := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.leftSweep_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.bottomHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.bottomHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.bottomHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.bottomHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.bottomHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.bottomHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.bottomHomotopy._proof_4 := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.bottomHomotopy._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.leftHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.leftHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.leftHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.leftHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.leftHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Kan.IntervalSquare.leftHomotopy._proof_3
