module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedBoundaryRecovery
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHornFilling

/-! # 全境界を保つ pinched 線形データ

概要：全ての面に厳密に一致し、全真部分集合で方程式を満たす成分族を作る。
方針：境界からの回収で最上位以外を定義し、各面の方程式を移送する。
規約：最上位の値は一旦零にする。使われ方：β3 の原始元による境界充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] {x y : D}

/-- 全境界から回収した、最上位を零とする線形族。 -/
def pinchedBoundaryKnownData {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData A x y (n + 1) := fun t =>
  if hf : t.val.1 ≠ Finset.univ then
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryRecoverComponent b t.val.1 t.val.2 t.property.1 t.property.2 hf
  else 0

/-- 面の部分集合の像は全体集合にならない。 -/
lemma pinchedBoundary_image_ne_univ {n : ℕ} (j : Fin (n + 2))
    (J : Finset (Fin (n + 1))) : J.image j.succAbove ≠ Finset.univ := by
  intro he
  have hj : j ∈ J.image j.succAbove := he.symm ▸ Finset.mem_univ j
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hj
  exact Fin.succAbove_ne j a ha

/-- 回収した線形データをどの面に制限しても、元の境界の面に戻る。 -/
lemma pinchedBoundaryKnownData_pullback_face {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (j : Fin (n + 2)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom (pinchedBoundaryKnownData b) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryFaceData b j := by
  funext t
  rcases t with ⟨⟨J, k⟩, hJ, hk⟩
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback j.succAboveOrderEmb.toOrderHom
    (pinchedBoundaryKnownData b)).component J k hJ hk =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryFaceData b j).component J k hJ hk
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pullback_component_of_inj _ _ _ _ _ _ j.succAboveOrderEmb.injective.injOn]
  have hf : J.image j.succAboveOrderEmb.toOrderHom ≠ Finset.univ :=
    pinchedBoundary_image_ne_univ j J
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.component, pinchedBoundaryKnownData, dite_eq_left hf]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryRecoverComponent_eq_face b _ _ _ _ hf j J hJ hk rfl

/-- 回収したデータは全ての真部分集合で線形削除方程式を満たす。 -/
lemma pinchedBoundaryKnownData_equation {n : ℕ}
    (b : (∂Δ[n + 1] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHom.pinchedHom A D x y)
    (I : Finset (Fin (n + 2))) (k : ℤ) (hI : I.Nonempty) (hk : k = 1 - (I.card : ℤ))
    (hfull : I ≠ Finset.univ) :
    _root_.SerrePositivity.DifferentialGraded.differential A ((pinchedBoundaryKnownData b).component I k hI hk) =
      (pinchedBoundaryKnownData b).rhs I k hk := by
  let i := Classical.choose hI
  have hm : I ≠ Finset.univ.erase i := by
    intro he
    exact Finset.notMem_erase i Finset.univ (he ▸ Classical.choose_spec hI)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHornFilling.equation_of_faces (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryHorn b i) _ _ I k hI hk hfull hm
  intro j hji
  exact (pinchedBoundaryKnownData_pullback_face b j).trans
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedBoundaryHorn_faceData b i j hji).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories
