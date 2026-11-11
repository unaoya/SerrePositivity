module
public import SerrePositivity.KST.Fibration.ZeroCategorySRealization
public import SerrePositivity.KST.Fibration.SpectrumZeroFromPositiveLevels
public import SerrePositivity.KST.SConstruction.DGKFixedSConstruction
public import SerrePositivity.KST.LocalizingInvariants.RelativeInvariant

/-! # 固定 dg K の ν に相対的な零保存と、元の相対 Verdier 四角形の零角

固定 S• 境界商比較と正段の整数 π 検出を使う。K の局所化性は入力しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.Spectra
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
variable (A : Type u) [CommRing A]

/-- ν(P) が零なら、同じ固定 BF 正段の一点への元の射は全段で局所化可逆。 -/
theorem dgKInputSpectrum_positive_toPoint_of_zero (P : PerfDGInput.{u, v} A)
    (hP : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue A P)) (r : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (toUnit (((dgKInputSpectrum A P).level (r + 1)).space).right)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have hs := boundaryReducedRealization_toPoint_localized_isIso_of_allZero r
    (stableCategoryModel (dgKInputStableValue A P)) hP
  have := dgKInputSBoundaryComparison_localized_isIso A r P
  have hc : IsIso (Q.map (dgKInputSBoundaryComparison A r P).right ≫
      Q.map (toUnit (((dgKInputSpectrum A P).level (r + 1)).space).right)) := by
    rw [← Q.map_comp, comp_toUnit]
    exact hs
  exact (isIso_comp_left_iff _ _).mp hc

/-- ν(P) の零性から、固定 K の同じ元の BF スペクトル頂点は Sp 内で零となる。 -/
theorem dgKInputK_vertex_isZero_of_zero (P : PerfDGInput.{u, v} A)
    (hP : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (dgKInputStableValue A P)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((dgKInputK A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex P)) := by
  have h := spectrum_isZeroVertex_of_positive_toPoint (dgKInputSpectrum A P)
    (dgKInputSpectrum_positive_toPoint_of_zero A P hP)
  exact (congrArg (fun z : Sp.{max (u + 1) v} _⦋0⦌ => _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex z)
    (dgKInputK_vertex A P)).mpr h

/-- 同じ固定 S 上の K は、ν が零とする元の全入力頂点を Sp の零頂点へ送る。 -/
theorem dgKInputK_preservesRelativeZero :
    PreservesRelativeZeroCategories (dgKInputNu.{u, v} A) (dgKInputK A) := by
  intro a ha
  obtain ⟨P, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertexEquiv (PerfDGInput.{u, v} A)).surjective a
  have he := congrArg (fun z : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableInfinity.{max (u + 1) v} _⦋0⦌ =>
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.IsZeroCategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject z)) (dgKInputNu_vertex A P)
  exact dgKInputK_vertex_isZero_of_zero A P (he.mp ha)

/-- 元の相対 Verdier 四角形を固定 K で写した同じ実四角形の零角。 -/
theorem dgRelativeK_zero_corner (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (d.square ≫ dgKInputK A) 0 1) :=
  dgKInputK_preservesRelativeZero A _ d.zero_corner

/-- 元の相対 Verdier 四角形の K 像を、その同じ全四角形と零角を保つ三角形として保持。 -/
def dgRelativeKZeroTriangle (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeVerdierDiagram (dgKInputNu.{u, v} A)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle Sp.{max (u + 1) v} where
  square := d.square ≫ dgKInputK A
  zero_corner := dgRelativeK_zero_corner A d

end SerrePositivity.KST.Fibration
