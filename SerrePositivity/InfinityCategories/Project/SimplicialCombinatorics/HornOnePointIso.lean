module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver

/-!
概要：一次元ホーンを、同じ一つの標準点と底上で同一視する。
方針：二頂点のホーン条件から全ての頂点が同じ番号となることを示す。
規約：元のホーンの包含と元の底への射を保持する。
使われ方：一次元境界のホーン側に零次元セルの分類比較を適用する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-- 一次元ホーンは同じ番号の一頂点の面そのもの。 -/
lemma hornOne_eq_faceSingleton (i : Fin 2) : horn.{u} 1 i = stdSimplex.face {i} := by
  ext ⟨⟨m⟩⟩ s
  rw [mem_horn_iff_notMem_range, stdSimplex.mem_face_iff]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, h⟩ k
    have hsk : s k ≠ j := fun hk ↦ h ⟨k, hk⟩
    omega
  · intro h
    have hi : i.rev ≠ i := by fin_cases i <;> decide
    refine ⟨i.rev, hi, ?_⟩
    rintro ⟨k, hk⟩
    exact hi ((h k).symm.trans hk).symm

/-- 同じ一つの標準点から元の一次元ホーンへの同型。 -/
def hornOnePointIso (i : Fin 2) : (Δ[0] : SSet.{u}) ≅ horn 1 i :=
  stdSimplex.faceSingletonIso i ≪≫ Subcomplex.eqToIso (hornOne_eq_faceSingleton i).symm

/-- 元のホーン側の同じ端点を、標準点上の写像として表示する。 -/
def hornOnePointMap {B : SSet.{u}} (i : Fin 2) (σ : (Δ[1] : SSet.{u}) ⟶ B) : Δ[0] ⟶ B :=
  (hornOnePointIso i).hom ≫ (horn 1 i).ι ≫ σ

/-- 同じ端点の標準点表示と元のホーンは、元の底上で同型。 -/
def hornOnePointOverIso {B : SSet.{u}} (i : Fin 2) (σ : (Δ[1] : SSet.{u}) ⟶ B) :
    Over.mk (hornOnePointMap i σ) ≅ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.HornBoundaryOver.horn 0 i σ :=
  Over.isoMk (hornOnePointIso i) rfl

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
