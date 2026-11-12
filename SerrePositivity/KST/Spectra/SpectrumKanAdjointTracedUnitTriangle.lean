module

public import SerrePositivity.KST.Spectra.PointedIhomIntervalAction
public import SerrePositivity.KST.Spectra.SpectrumKanAdjointTracedUnitCoordinates

/-!
概要：トレース付き単位の同じ実二単体を、元の全 Hom の構造比較の二単体へ移す。
方針：内部 Hom の作用と同じ懸垂評価への制限だけを後合成する。
規約：二単体を選び直さない。使われ方：共通の非定数境界を持つ二つの正方形の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable (X Y : OmegaSpectrum.{u}) {A : PointedSimplicialSet.{u}}
  (φ : A ⟶ pointedSpace X Y.toKanSequence)

/-- 単位の構造 Hom の区間・二単体を、同じ全パラメータの構造 Hom へ移す射。 -/
def kanAdjointTracedUnitStructureAction (n : ℕ) :
    PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (Y.level n).space)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space ⟶
    PointedObject.basedHom A (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space) :=
  PointedMapping.ihomAction (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (Y.level n).space)
    ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space ≫
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (kanAdjointStructureInput X Y φ n)
    (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space)

/-- 同じ単位の実三角形を、元の全 Hom の同じ懸垂評価へ移した二単体。 -/
def kanAdjointTracedUnitParameterTriangle (n : ℕ) :=
  SSet.yonedaEquiv.symm (OmegaSpectrum.tracedSignedLoopUnitTriangle Y n).simplex ≫
    (kanAdjointTracedUnitStructureAction X Y φ n).right

/-- 第一辺は、既存の全 Hom 比較が持つ同じ構造区間そのもの。 -/
lemma kanAdjointTracedUnitParameterTriangle_two (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ kanAdjointTracedUnitParameterTriangle X Y φ n =
      (kanAdjointParameterStructureInterval X Y φ n).path := by
  rw [kanAdjointTracedUnitParameterTriangle, ← Category.assoc,
    SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  change SSet.yonedaEquiv.symm
      (SSet.yonedaEquiv (OmegaSpectrum.signedLoopUnitStructurePath Y n).path) ≫ _ = _
  rw [Equiv.symm_apply_apply]
  exact (PointedMapping.VerticalPath.basedIhomMap_pre_path
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (OmegaSpectrum.signedLoopUnitStructurePath Y n)
      (kanAdjointStructureInput X Y φ n)).symm.trans
        (kanAdjointParameterStructureInterval_unit_path X Y φ n).symm

/-- 第二辺も、単位に保持した同じ前段の懸垂・構造像の実区間を写したもの。 -/
lemma kanAdjointTracedUnitParameterTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ kanAdjointTracedUnitParameterTriangle X Y φ n =
      (OmegaSpectrum.tracedSignedLoopUnitStepInterval Y n).path ≫
        (kanAdjointTracedUnitStructureAction X Y φ n).right := by
  rw [kanAdjointTracedUnitParameterTriangle, ← Category.assoc,
    SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  change SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (OmegaSpectrum.tracedSignedLoopUnitStepInterval Y n).path) ≫ _ = _
  rw [Equiv.symm_apply_apply]

/-- 対角辺は、元の次段延長区間の構造制限を写した同じ実区間。 -/
lemma kanAdjointTracedUnitParameterTriangle_one (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ kanAdjointTracedUnitParameterTriangle X Y φ n =
      (OmegaSpectrum.tracedSignedLoopUnitRestrictionInterval Y n).path ≫
        (kanAdjointTracedUnitStructureAction X Y φ n).right := by
  rw [kanAdjointTracedUnitParameterTriangle, ← Category.assoc,
    SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm]
  change SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (OmegaSpectrum.tracedSignedLoopUnitRestrictionInterval Y n).path) ≫ _ = _
  rw [Equiv.symm_apply_apply]

end SerrePositivity.KST.Spectra.RawSpectrumMapping
