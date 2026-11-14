module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.ProperEquationBianchi
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinBoundary

/-! # dg nerve の全境界の単体データへの回収

概要：実際の全境界写像から対象・全真部分集合の射を回収し、最上位だけを零とする。
方針：全ての面を選ぶ SelectedFaceAssembly を使う。
規約：全真部分集合の方程式を証明する。使われ方：β3 の収縮頂点の始対象性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
open scoped _root_.Simplicial
variable {A : Type u} [CommRing A] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory A D]

/-- 全面を選んだ領域から標準単体の境界への包含。 -/
def dgBoundaryRegionInclusion (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region (Finset.univ : Finset (Fin (n + 1))) : SSet.{t}) ⟶ ∂Δ[n] :=
  Subcomplex.homOfLE (by
    intro m s hs
    obtain ⟨j, _, hj⟩ := hs
    change ¬ Function.Surjective (SSet.stdSimplex.asOrderHom s)
    intro he
    obtain ⟨k, hk⟩ := he j
    exact hj k hk)

/-- 全面の族は全ての頂点を覆う。 -/
lemma dgBoundaryCoversVertices (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceData.CoversVertices (Finset.univ : Finset (Fin (n + 3))) := by
  intro k
  obtain ⟨j, hj⟩ := exists_ne k
  exact ⟨j, Finset.mem_univ j, hj⟩

/-- 全境界写像を全面の領域からの写像とみなす。 -/
def dgBoundaryRegion {n : ℕ} (b : (∂Δ[n + 2] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.region (Finset.univ : Finset (Fin (n + 3))) : SSet.{max u v}) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D := dgBoundaryRegionInclusion.{max u v} (n + 2) ≫ b

/-- 全面の領域での面の値は、元の境界写像の面の値と一致する。 -/
lemma dgBoundaryRegion_face {n : ℕ}
    (b : (∂Δ[n + 2] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (j : Fin (n + 3)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBoundaryRegion b).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaces.face Finset.univ j (Finset.mem_univ j)) =
      SSet.yonedaEquiv (SSet.boundary.ι j ≫ b) := by
  rw [SSet.yonedaEquiv_comp]
  change b.app _ _ = b.app _ _
  congr 1

/-- 全境界から回収し、唯一の最上位射を零とした単体データ。 -/
def dgBoundaryZeroData {n : ℕ} (b : (∂Δ[n + 2] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData A D (n + 2) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData Finset.univ (dgBoundaryCoversVertices n) (dgBoundaryRegion b)
    (fun _ _ _ _ _ _ _ _ => 0)

/-- 境界から回収したデータをどの面に制限しても、元の面に戻る。 -/
lemma dgBoundaryZeroData_pullback_face {n : ℕ}
    (b : (∂Δ[n + 2] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (j : Fin (n + 3)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBoundaryZeroData b).pullback j.succAboveOrderEmb.toOrderHom =
      (SSet.yonedaEquiv (SSet.boundary.ι j ≫ b)).toSimplexData := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData _ _ _ _).pullback _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData_pullback_face _ _ _ _ j (Finset.mem_univ j),
    dgBoundaryRegion_face]

/-- 回収したデータは全真部分集合で dg nerve の方程式を満たす。 -/
lemma dgBoundaryZeroData_proper_equation {n : ℕ}
    (b : (∂Δ[n + 2] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D)
    (I : Finset (Fin (n + 3))) (hI : I ≠ Finset.univ) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBoundaryZeroData b).Equation I := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SelectedFaceAssembly.assembleData_equation
  obtain ⟨j, hj⟩ : ∃ j, j ∉ I := by
    simpa only [ne_eq, Finset.eq_univ_iff_forall, not_forall] using hI
  exact ⟨j, Finset.mem_univ j, hj⟩

/-- 最初の頂点を固定した境界では、回収した最初の対象もその dg 対象。 -/
lemma dgBoundaryZeroData_first_obj {n : ℕ}
    (b : (∂Δ[n + 2] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D) (x : D)
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex (n + 1) 0 ≫ b = SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x)) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgBoundaryZeroData b).obj 0 = x := by
  have hh := congrArg
    (fun F : (Δ[0] : SSet.{max u v}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve A D =>
      (SSet.yonedaEquiv F : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex A D 0).obj 0) hb
  exact hh

end SerrePositivity.InfinityCategories.Project.DerivedCategories
