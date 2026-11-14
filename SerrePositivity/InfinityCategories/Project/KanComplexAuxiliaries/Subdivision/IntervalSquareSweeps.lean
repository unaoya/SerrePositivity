module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
概要：正方形の下辺・左辺を共通の対角辺へ動かす二つの単体的な変形を構成する。
方針：二つの区間座標の最小値を用い、(s,min(s,t)) と (min(s,t),s) を取る。
規約：s が経路、t がホモトピーの時間。使われ方：円評価の二つの Hom 経路の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.IntervalSquare
end SerrePositivity.KST.Spectra.IntervalSquare
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra.IntervalSquare

/-- 区間の二座標の最小値。 -/
def meet : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] where
  app _ := ↾fun ab ↦ stdSimplex.objMk
    ⟨fun i ↦ min (stdSimplex.asOrderHom ab.1 i) (stdSimplex.asOrderHom ab.2 i),
      fun _ _ h ↦ min_le_min ((stdSimplex.asOrderHom ab.1).monotone h)
        ((stdSimplex.asOrderHom ab.2).monotone h)⟩
  naturality := by
    rintro ⟨⟨n⟩⟩ ⟨⟨m⟩⟩ α
    apply ConcreteCategory.hom_ext
    intro ab
    apply stdSimplex.ext
    intro i
    rfl

/-- 下辺から対角への変形。 -/
def bottomSweep : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[1] :=
  lift (fst _ _) _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet

/-- 左辺から対角への変形。 -/
def leftSweep : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ Δ[1] ⊗ Δ[1] :=
  lift _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet (fst _ _)

/-- 最小値の時間零での制限は零。 -/
lemma meet_zero :
    SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet.{u} = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  change min (a i) 0 = 0
  exact min_eq_right (Fin.zero_le _)

/-- 最小値の時間一での制限は元の経路座標。 -/
lemma meet_one : SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet.{u} = 𝟙 (Δ[1] : SSet.{u}) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  change min (a i) 1 = a i
  exact min_eq_left (Fin.le_last _)

/-- 最小値の経路零での制限は零。 -/
lemma meet_source :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  change min 0 (a i) = 0
  exact min_eq_left (Fin.zero_le _)

/-- 最小値の経路一での制限は時間座標。 -/
lemma meet_target :
    lift (SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) ≫
        _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet = 𝟙 (Δ[1] : SSet.{u}) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  apply stdSimplex.ext
  intro i
  change min 1 (a i) = a i
  exact min_eq_right (Fin.le_last _)

/-- 下辺変形の時間零は元の下辺。 -/
lemma bottomSweep_zero :
    SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomSweep.{u} =
      lift (𝟙 (Δ[1] : SSet.{u})) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomSweep, comp_lift, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet_zero]
  rfl

/-- 下辺変形の時間一は共通の対角。 -/
lemma bottomSweep_one :
    SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomSweep.{u} = lift (𝟙 (Δ[1] : SSet.{u})) (𝟙 _) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomSweep, comp_lift, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet_one]
  rfl

/-- 左辺変形の時間零は元の左辺。 -/
lemma leftSweep_zero :
    SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftSweep.{u} =
      lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2))) (𝟙 (Δ[1] : SSet.{u})) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftSweep, comp_lift, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet_zero]
  rfl

/-- 左辺変形の時間一も共通の対角。 -/
lemma leftSweep_one :
    SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftSweep.{u} = lift (𝟙 (Δ[1] : SSet.{u})) (𝟙 _) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftSweep, comp_lift, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet_one]
  rfl

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomSweep (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.bottomSweep := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomSweep

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.bottomSweep_one := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomSweep_one

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.bottomSweep_zero := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomSweep_zero

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftSweep (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.leftSweep := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftSweep

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.leftSweep_one := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftSweep_one

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.leftSweep_zero := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftSweep_zero

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.meet := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.meet_one := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet_one

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.meet_source := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet_source

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.meet_target := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.meet_zero := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet_zero

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.bottomSweep.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.bottomSweep.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.leftSweep.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.leftSweep.eq_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.meet._proof_1 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Spectra.IntervalSquare.meet._proof_2 := _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.meet._proof_2
