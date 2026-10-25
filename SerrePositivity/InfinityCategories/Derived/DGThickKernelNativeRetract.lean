module
public import SerrePositivity.InfinityCategories.Derived.DGNativeTriaRetract
public import SerrePositivity.InfinityCategories.Derived.DGNativeDerivedFiniteCell
public import SerrePositivity.InfinityCategories.Derived.DGQuotientThickKernelCriterion
public import SerrePositivity.InfinityCategories.Stable.UniverseHomotopyRetract
public import SerrePositivity.InfinityCategories.Stable.UniverseVertexClosure
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  [IsDGPretriangulated R D]

lemma dgThickClosureProperty_iff_nativeStableRetract (P : Set D) (x : D) :
    dgThickClosureProperty R D P x ↔ ∃ y : D,
      StableVertexClosure (X := dgNerve R D) (Simplex.vertex '' P) (Simplex.vertex y) ∧
      Nonempty (Retract (SSet.HomotopyCategory.mk (X := dgNerve R D) (Simplex.vertex x))
        (SSet.HomotopyCategory.mk (X := dgNerve R D) (Simplex.vertex y))) := by
  constructor
  · rintro ⟨Z, hZ, ⟨r⟩⟩
    obtain ⟨y, ⟨e⟩⟩ := dgTria_isRepresentable R D Z
    have hy : triaImage R D P (triaRepresentable R D y) :=
      (triaImage R D P).prop_of_iso e hZ
    refine ⟨y, (dgNative_stableVertexClosure_iff_derivedFiniteCell R D P y).mpr hy, ?_⟩
    exact (dgNative_retract_iff_tria_retract R D x y).mpr
      ⟨r.trans (Retract.ofIso e)⟩
  · rintro ⟨y, hy, hr⟩
    exact ⟨triaRepresentable R D y,
      (dgNative_stableVertexClosure_iff_derivedFiniteCell R D P y).mp hy,
      (dgNative_retract_iff_tria_retract R D x y).mp hr⟩

lemma dgThickClosureProperty_iff_uliftStableRetract (P : Set D) (x : D) :
    dgThickClosureProperty R D P x ↔ ∃ y : D,
      StableVertexClosure (X := (SSet.uliftFunctor.{w}).obj (dgNerve R D))
        (ULift.up '' (Simplex.vertex '' P)) (ULift.up (Simplex.vertex y)) ∧
      Nonempty (Retract
        (SSet.HomotopyCategory.mk (X := (SSet.uliftFunctor.{w}).obj (dgNerve R D))
          (ULift.up (Simplex.vertex x)))
        (SSet.HomotopyCategory.mk (X := (SSet.uliftFunctor.{w}).obj (dgNerve R D))
          (ULift.up (Simplex.vertex y)))) := by
  rw [dgThickClosureProperty_iff_nativeStableRetract]
  constructor
  · rintro ⟨y, hy, hr⟩
    exact ⟨y, (stableVertexClosure_ulift_iff _ _).mpr hy,
      (homotopyRetract_ulift_iff _ _).mpr hr⟩
  · rintro ⟨y, hy, hr⟩
    exact ⟨y, (stableVertexClosure_ulift_iff _ _).mp hy,
      (homotopyRetract_ulift_iff _ _).mp hr⟩

end SerrePositivity.InfinityCategories
