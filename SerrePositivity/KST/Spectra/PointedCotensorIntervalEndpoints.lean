module

public import SerrePositivity.KST.Spectra.PointedCotensorFamilyDescription
public import SerrePositivity.KST.Spectra.PointedCotensorFamilyNaturality
public import SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.FreeIntervalBoundary
public import SerrePositivity.KST.Spectra.RawSpectrumParameterRestriction
public import SerrePositivity.KST.Spectra.PointedRelativeTransposePaths

/-!
概要：元の実区間を自由区間値の射へ移し、両端評価を元の二つの射へ厳密に戻す。
方針：自由基点の随伴と転置による表示を、零次単位族の式で評価する。
規約：同じ実区間の全体を使用。使われ方：全列区間の指定境界。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra
namespace PointedCotensorCoordinates

/-- 零次単位族を移して単位で評価すると、同じ点つき射に戻る。 -/
lemma family_pointFamily_unit {T E : PointedSimplicialSet.{u}} (f : T ⟶ E) :
    family (PointedMapping.pointFamily f) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed PointedSimplicialSet.adjoinBasepointDeltaZeroIso.inv E ≫
      (unitIsoSelf (X := E)).hom = f := by
  let z := (PointedObject.adjoinHomEquiv (Δ[0] : SSet.{u})
    (PointedObject.basedHom T E)).symm (PointedMapping.pointFamily f)
  have hz : PointedSimplicialSet.adjoinBasepointDeltaZeroIso.inv ≫ z = curry' f := by
    apply (PointedObject.adjoinHomEquiv (𝟙_ SSet.{u}) (PointedObject.basedHom T E)).injective
    have hi : (coprod.inl : 𝟙_ SSet.{u} ⟶ (𝟙_ PointedSimplicialSet.{u}).right) ≫
        PointedSimplicialSet.adjoinBasepointDeltaZeroIso.inv.right =
      PointedSimplicialSet.deltaZeroUnitIso.inv ≫
        (coprod.inl : (Δ[0] : SSet.{u}) ⟶ (PointedObject.adjoin (Δ[0] : SSet.{u})).right) := by
      exact coprod.inl_map _ _
    change coprod.inl ≫ (PointedSimplicialSet.adjoinBasepointDeltaZeroIso.inv.right ≫
      z.right) = _
    rw [← Category.assoc, hi, Category.assoc]
    change PointedSimplicialSet.deltaZeroUnitIso.inv ≫
      (PointedObject.adjoinHomEquiv _ _ z) = _
    rw [Equiv.apply_symm_apply, PointedMapping.pointFamily_closed,
      Iso.inv_hom_id_assoc]
    rfl
  rw [family_eq_transpose]
  change PointedMapping.transpose z ≫ _ ≫ _ = _
  rw [← Category.assoc, ← PointedMapping.transpose_pre_outer, hz]
  apply curry'_injective
  rw [← PointedMapping.transpose_unit, PointedMapping.transpose_transpose]

end PointedCotensorCoordinates
namespace PointedMapping.VerticalPath

/-- 元の同じ実区間を、自由区間の cotensor を値とする点つき射へ表示する。 -/
def freeMap {T E : PointedSimplicialSet.{u}} {f g : T ⟶ E}
    (P : PointedMapping.VerticalPath (PointedObject.toPoint E) f g) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathSpace E := PointedCotensorCoordinates.family P.path

/-- 自由区間の任意の端点評価は、元の区間の同じ面の単位評価。 -/
lemma freeMap_endpoint {T E : PointedSimplicialSet.{u}} {f g : T ⟶ E}
    (P : PointedMapping.VerticalPath (PointedObject.toPoint E) f g) (i : Fin 2) :
    P.freeMap ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint E i =
    PointedCotensorCoordinates.family (stdSimplex.δ i ≫ P.path) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed PointedSimplicialSet.adjoinBasepointDeltaZeroIso.inv E ≫
        (unitIsoSelf (X := E)).hom := by
  rw [freeMap, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.freeIntervalEndpoint, ← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp]
  rw [← Category.assoc, ← Category.assoc]
  erw [PointedCotensorCoordinates.family_parameter (stdSimplex.δ i) P.path]
  exact Category.assoc _ _ _

/-- 始点評価は、元の始点の点つき射そのもの。 -/
lemma freeMap_start {T E : PointedSimplicialSet.{u}} {f g : T ⟶ E}
    (P : PointedMapping.VerticalPath (PointedObject.toPoint E) f g) :
    P.freeMap ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint E 1 = f := by
  rw [freeMap_endpoint, P.zero, PointedCotensorCoordinates.family_pointFamily_unit]

/-- 終点評価も、元の終点の点つき射そのもの。 -/
lemma freeMap_finish {T E : PointedSimplicialSet.{u}} {f g : T ⟶ E}
    (P : PointedMapping.VerticalPath (PointedObject.toPoint E) f g) :
    P.freeMap ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.freePathEndpoint E 0 = g := by
  rw [freeMap_endpoint, P.one, PointedCotensorCoordinates.family_pointFamily_unit]

end PointedMapping.VerticalPath
end SerrePositivity.KST.Spectra
