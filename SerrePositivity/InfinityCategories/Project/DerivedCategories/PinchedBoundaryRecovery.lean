module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHornData
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-! # Pinched Hom の全境界からの成分回収

概要：非空な真部分集合の成分を、実際の全境界の写像から回収する。
方針：集合内の一点を欠くホーンへ制限し、既存の回収の面の選択独立性を使う。
規約：包含する任意の面の成分に一致する。使われ方：β3 の全境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- ホーンから全境界への包含。 -/
def pinchedHornBoundaryInclusion {n : ℕ} (i : Fin (n + 1)) :
    (Λ[n, i] : SSet.{t}) ⟶ ∂Δ[n] :=
  Subcomplex.homOfLE (by
    rw [SSet.horn_eq_iSup]
    exact iSup_le (fun j => SSet.face_singleton_compl_le_boundary j.val))

/-- 全境界写像を一つのホーンに制限する。 -/
def pinchedBoundaryHorn {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (i : Fin (n + 2)) : (Λ[n + 1, i] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y :=
  pinchedHornBoundaryInclusion.{max u v} i ≫ b

/-- 全境界の指定面の線形データ。 -/
def pinchedBoundaryFaceData {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (j : Fin (n + 2)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y n :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData (SSet.yonedaEquiv (SSet.boundary.ι j ≫ b))

/-- ホーンへの制限は利用可能な面のデータを変えない。 -/
lemma pinchedBoundaryHorn_faceData {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (i j : Fin (n + 2)) (hji : j ≠ i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.faceData (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryHorn b i) j hji = _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryFaceData b j := by
  apply congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.toLinearData
  rw [SSet.yonedaEquiv_comp]
  change b.app _ _ = b.app _ _
  congr 1

/-- 境界から、全体集合以外の非空成分を回収する。 -/
def pinchedBoundaryRecoverComponent {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (I : Finset (Fin (n + 2))) (k : ℤ) (hI : I.Nonempty) (hk : k = 1 - (I.card : ℤ))
    (hfull : I ≠ Finset.univ) : _root_.SerrePositivity.DifferentialGraded.GradedHom A x y k := by
  let i := Classical.choose hI
  have hi : i ∈ I := Classical.choose_spec hI
  have hm : I ≠ Finset.univ.erase i := by
    intro he
    exact Finset.notMem_erase i Finset.univ (he ▸ hi)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.recoverComponent (pinchedBoundaryHorn b i) I k hI hk hfull hm

/-- 回収した成分は、それを含む任意の面の成分に一致する。 -/
lemma pinchedBoundaryRecoverComponent_eq_face {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (I : Finset (Fin (n + 2))) (k : ℤ) (hI : I.Nonempty) (hk : k = 1 - (I.card : ℤ))
    (hfull : I ≠ Finset.univ) (j : Fin (n + 2)) (J : Finset (Fin (n + 1)))
    (hJ : J.Nonempty) (hk' : k = 1 - (J.card : ℤ)) (hImage : J.image j.succAbove = I) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryRecoverComponent b I k hI hk hfull =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryFaceData b j).component J k hJ hk' := by
  unfold pinchedBoundaryRecoverComponent
  have hji : j ≠ Classical.choose hI := by
    intro he
    have hj : j ∈ I := he.symm ▸ Classical.choose_spec hI
    rw [← hImage] at hj
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hj
    exact Fin.succAbove_ne j a ha
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.recoverComponent_eq_face _ _ _ _ _ _ _ j hji J hJ hk' hImage,
    pinchedBoundaryHorn_faceData]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
