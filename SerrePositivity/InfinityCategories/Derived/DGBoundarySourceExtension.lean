module
public import SerrePositivity.InfinityCategories.Derived.DGBoundarySourcePrimitive

/-! # 収縮する始点を持つ dg nerve の全境界の延長

概要：全境界から回収した最初の対象が収縮するとき、全境界を実際に充填する。
方針：最上位の原始元を挿入した単体の面を計算し、境界の外延性で貼り合わせる。
規約：次元二以上の全境界。使われ方：β3 の収縮頂点の始対象性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 全境界と最初の対象の収縮元から得る実際の充填単体。 -/
def dgBoundarySourceExtensionSimplex {n : ℕ}
    (b : (∂Δ[n + 2] : SSet.{max u v}) ⟶ dgNerve A D)
    (h : GradedHom A ((dgBoundaryZeroData b).obj 0) ((dgBoundaryZeroData b).obj 0) (-1))
    (dh : (homObject A D ((dgBoundaryZeroData b).obj 0) ((dgBoundaryZeroData b).obj 0)).d
      (-1) 0 h = (unitElement A ((dgBoundaryZeroData b).obj 0)).val) : Simplex A D (n + 2) :=
  dgBoundarySourceFiller (dgBoundaryZeroData b) (dgBoundaryZeroData_proper_equation b) h dh

/-- 実際の充填単体の全ての面は元の境界の面に一致する。 -/
lemma dgBoundarySourceExtensionSimplex_face {n : ℕ}
    (b : (∂Δ[n + 2] : SSet.{max u v}) ⟶ dgNerve A D)
    (h : GradedHom A ((dgBoundaryZeroData b).obj 0) ((dgBoundaryZeroData b).obj 0) (-1))
    (dh : (homObject A D ((dgBoundaryZeroData b).obj 0) ((dgBoundaryZeroData b).obj 0)).d
      (-1) 0 h = (unitElement A ((dgBoundaryZeroData b).obj 0)).val) (j : Fin (n + 3)) :
    (dgNerve A D).δ j (dgBoundarySourceExtensionSimplex b h dh) =
      SSet.yonedaEquiv (SSet.boundary.ι j ≫ b) := by
  apply Simplex.ext
  exact (dgBoundarySourceFillerData_pullback_face (dgBoundaryZeroData b) h j).trans
    (dgBoundaryZeroData_pullback_face b j)

/-- 収縮する始点を持つ全境界は標準単体へ延長する。 -/
lemma dgBoundarySourceExtension {n : ℕ}
    (b : (∂Δ[n + 2] : SSet.{max u v}) ⟶ dgNerve A D)
    (h : GradedHom A ((dgBoundaryZeroData b).obj 0) ((dgBoundaryZeroData b).obj 0) (-1))
    (dh : (homObject A D ((dgBoundaryZeroData b).obj 0) ((dgBoundaryZeroData b).obj 0)).d
      (-1) 0 h = (unitElement A ((dgBoundaryZeroData b).obj 0)).val) :
    ∃ F : (Δ[n + 2] : SSet.{max u v}) ⟶ dgNerve A D, (∂Δ[n + 2]).ι ≫ F = b := by
  refine ⟨SSet.yonedaEquiv.symm (dgBoundarySourceExtensionSimplex b h dh), ?_⟩
  apply SSet.boundary.hom_ext
  intro j
  rw [← Category.assoc, SSet.boundary.ι_ι, SSet.stdSimplex.δ_comp_yonedaEquiv_symm,
    dgBoundarySourceExtensionSimplex_face, Equiv.symm_apply_apply]

end SerrePositivity.InfinityCategories
