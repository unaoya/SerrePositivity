module

public import SerrePositivity.AlgebraicGeometry.SchemeBlowupAway
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
概要：閉部分スキームの中心の像を、元の基底の真に小さい閉集合にする。
方針：閉埋め込みの閉写像性と単射性、中心外の稠密性を使う。
規約：元の中心の厚みは変えず、支持の像だけを帰納の添字に用いる。
使われ方：Noether閉像の帰納（承認済み計画I05・I06）。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u

/-- 元の閉埋め込みによる中心の支持の閉像。 -/
def closedCenterImage {S Y : Scheme.{u}} (j : Y ⟶ S) [IsClosedImmersion j]
    (J : Y.IdealSheafData) : TopologicalSpace.Closeds S :=
  ⟨j '' (J.support : Set Y), j.isClosedEmbedding.isClosedMap _ J.support.isClosed⟩

/-- 非空な閉部分の稠密な中心外は、その中心像を真に小さくする。 -/
theorem closedCenterImage_lt
    {S Y : Scheme.{u}} (j : Y ⟶ S) [IsClosedImmersion j] [Nonempty Y]
    (C : TopologicalSpace.Closeds S) (hj : Set.range j = (C : Set S))
    (J : Y.IdealSheafData) (hJ : Dense (centerComplement J).carrier) :
    closedCenterImage j J < C := by
  apply lt_of_le_of_ne
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change j y ∈ (C : Set S)
    rw [← hj]
    exact Set.mem_range_self y
  · intro he
    obtain ⟨y, hy⟩ := hJ.nonempty
    have hyC : j y ∈ (C : Set S) := by rw [← hj]; exact Set.mem_range_self y
    have hyJ : j y ∈ (closedCenterImage j J : Set S) := by rw [he]; exact hyC
    obtain ⟨z, hz, hzy⟩ := hyJ
    have hzY : z = y := j.isClosedEmbedding.injective hzy
    subst z
    exact hy hz

end SerrePositivity.AlgebraicGeometry
