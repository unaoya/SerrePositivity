module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNativeTriaRetract
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNativeDerivedFiniteCell
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientThickKernelCriterion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniverseHomotopyRetract
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.UniverseVertexClosure
/-!
概要：tria の thick 核は実安定閉包の対象の、元の dg nerve の h 圏での retract と一致する。
方針：前三角性で有限 cell を代表対象に戻し、完全忠実な native h と tria の比較で分裂式を移す。
規約：retract を旧安定閉包へ追加せず、新しい同値判定として公開する。
使われ方：D-16 追加 (3) の D2 f③。任意の追加 ULift 宇宙も同じ対象で扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
  [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D]

lemma dgThickClosureProperty_iff_nativeStableRetract (P : Set D) (x : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty R D P x ↔ ∃ y : D,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) ∧
      Nonempty (Retract (SSet.HomotopyCategory.mk (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
        (SSet.HomotopyCategory.mk (X := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y))) := by
  constructor
  · rintro ⟨Z, hZ, ⟨r⟩⟩
    obtain ⟨y, ⟨e⟩⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgTria_isRepresentable R D Z
    have hy : _root_.SerrePositivity.DifferentialGraded.triaImage R D P (_root_.SerrePositivity.DifferentialGraded.triaRepresentable R D y) :=
      (_root_.SerrePositivity.DifferentialGraded.triaImage R D P).prop_of_iso e hZ
    refine ⟨y, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNative_stableVertexClosure_iff_derivedFiniteCell R D P y).mpr hy, ?_⟩
    exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNative_retract_iff_tria_retract R D x y).mpr
      ⟨r.trans (Retract.ofIso e)⟩
  · rintro ⟨y, hy, hr⟩
    exact ⟨_root_.SerrePositivity.DifferentialGraded.triaRepresentable R D y,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNative_stableVertexClosure_iff_derivedFiniteCell R D P y).mp hy,
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNative_retract_iff_tria_retract R D x y).mp hr⟩

lemma dgThickClosureProperty_iff_uliftStableRetract (P : Set D) (x : D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgThickClosureProperty R D P x ↔ ∃ y : D,
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.StableVertexClosure (X := (SSet.uliftFunctor.{w}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D))
        (ULift.up '' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex '' P)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)) ∧
      Nonempty (Retract
        (SSet.HomotopyCategory.mk (X := (SSet.uliftFunctor.{w}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D))
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)))
        (SSet.HomotopyCategory.mk (X := (SSet.uliftFunctor.{w}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D))
          (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)))) := by
  rw [dgThickClosureProperty_iff_nativeStableRetract]
  constructor
  · rintro ⟨y, hy, hr⟩
    exact ⟨y, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableVertexClosure_ulift_iff _ _).mpr hy,
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyRetract_ulift_iff _ _).mpr hr⟩
  · rintro ⟨y, hy, hr⟩
    exact ⟨y, (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableVertexClosure_ulift_iff _ _).mp hy,
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.homotopyRetract_ulift_iff _ _).mp hr⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories
