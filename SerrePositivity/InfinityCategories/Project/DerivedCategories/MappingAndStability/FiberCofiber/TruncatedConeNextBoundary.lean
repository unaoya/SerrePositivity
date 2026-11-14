module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FiberCofiber.TruncatedConeNextFaces
public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryFaceGluing

/-! # 有限次数錐からの次次数の実境界写像

概要：元の次次数図式単体と、既存の錐の全指定面を実境界写像として貼り合わせる。
方針：全面の整合性を米田表示へ移し、標準境界の多重余等化子に渡す。
規約：全ての面を厳密に保持。使われ方：次次数の有限同時実充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
variable {K X : SSet.{u}} {f : K ⟶ X} {N : ℕ} (C : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.TruncatedJoinConeData f N)

/-- 次次数の錐に指定する全面の米田表示。 -/
def truncatedConeNextBoundaryFace (σ : K _⦋N + 1⦌) (j : Fin (N + 3)) : Δ[N + 1] ⟶ X :=
  (SSet.yonedaEquiv (X := X)).symm (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNextFace C σ j)

/-- 全面の米田表示は、標準境界の共有面上で整合する。 -/
lemma truncatedConeNextBoundaryFace_compatible (σ : K _⦋N + 1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryFaceCompatible (truncatedConeNextBoundaryFace C σ) := by
  intro j k hjk
  apply (SSet.yonedaEquiv (X := X)).injective
  simp only [truncatedConeNextBoundaryFace, stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.truncatedConeNextFace_compatible C σ j k hjk

/-- 次次数の各図式単体に指定する、実際の全境界写像。 -/
def truncatedConeNextBoundary (σ : K _⦋N + 1⦌) : (∂Δ[N + 2] : SSet.{u}) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.boundaryFaceGluing (truncatedConeNextBoundaryFace_compatible C σ)

/-- 実境界写像は、元の指定全面の米田表示を厳密に保つ。 -/
lemma truncatedConeNextBoundary_face (σ : K _⦋N + 1⦌) (j : Fin (N + 3)) :
    boundary.ι j ≫ truncatedConeNextBoundary C σ = truncatedConeNextBoundaryFace C σ j :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.boundaryFaceGluing_face _ j

/-- 指定零面は、元の同じ図式単体のまま。 -/
lemma truncatedConeNextBoundary_face_zero (σ : K _⦋N + 1⦌) :
    boundary.ι (0 : Fin (N + 3)) ≫ truncatedConeNextBoundary C σ =
      (SSet.yonedaEquiv (X := X)).symm (f.app _ σ) :=
  truncatedConeNextBoundary_face C σ 0

/-- 指定正番号面は、同じ下次数の錐単体である。 -/
lemma truncatedConeNextBoundary_face_positive (σ : K _⦋N + 1⦌) (i : Fin (N + 2)) :
    boundary.ι i.succ ≫ truncatedConeNextBoundary C σ =
      (SSet.yonedaEquiv (X := X)).symm (C.simplex N le_rfl (K.δ i σ)) :=
  truncatedConeNextBoundary_face C σ i.succ

end SerrePositivity.InfinityCategories.Project.DerivedCategories
