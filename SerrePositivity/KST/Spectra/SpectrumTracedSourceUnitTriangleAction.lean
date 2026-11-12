module

public import SerrePositivity.KST.Spectra.PointedPrecompositionAction
public import SerrePositivity.KST.Spectra.SpectrumTracedSourceActionCoordinates

/-!
概要：源単位の保存済み実三角形を、同じ全パラメータの構造 Hom へ移す。
方針：符号付き loop の列射を転置し、前合成の単一の射へ入力する。
規約：実二単体と三辺を選び直さない。使われ方：源単位側の構造正方形の指定境界。
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

/-- 元の全パラメータ列射の同じ次段の符号付き loop 作用を転置した入力。 -/
def tracedSourceUnitStructureInput (n : ℕ) :
    A ⟶ PointedObject.basedHom
      ((KanSequence.signedLoopTail X.toKanSequence).level (n + 1)).space
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space :=
  PointedMapping.transpose
    ((KanSequence.signedLoopParameterHom (homOfParameterFamily X Y.toKanSequence A φ)).app
      (n + 1))

/-- 同じ源の構造 Hom を、同じ全パラメータの構造 Hom へ送る単一の前合成射。 -/
def tracedSourceUnitStructureAction (n : ℕ) :
    PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.signedLoopTail X.toKanSequence).level (n + 1)).space ⟶
    PointedObject.basedHom A (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space) :=
  PointedMapping.preParameterAction (tracedSourceUnitStructureInput X Y φ n) (𝟙 A)

/-- 同じ構造作用は、元のパラメータ付き列射への後合成と転置そのもの。 -/
lemma tracedSourceUnitStructureAction_post (n : ℕ) :
    tracedSourceUnitStructureAction X Y φ n =
      PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
        ((KanSequence.signedLoopParameterHom
          (homOfParameterFamily X Y.toKanSequence A φ)).app (n + 1)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomExchange.iso (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) A
        ((KanSequence.signedLoopTail Y.toKanSequence).level (n + 1)).space).hom := by
  rw [tracedSourceUnitStructureAction, PointedMapping.preParameterAction_id,
    tracedSourceUnitStructureInput, PointedMapping.transpose_transpose]

/-- 源単位に保存した同じ実二単体の全パラメータ像。 -/
def tracedSourceUnitParameterTriangle (n : ℕ) :=
  SSet.yonedaEquiv.symm (OmegaSpectrum.tracedSignedLoopUnitTriangle X n).simplex ≫
    (tracedSourceUnitStructureAction X Y φ n).right

/-- 第一辺は元の源単位の構造入力区間の全パラメータ前合成そのもの。 -/
lemma tracedSourceUnitParameterTriangle_two (n : ℕ) :
    stdSimplex.δ (2 : Fin 3) ≫ tracedSourceUnitParameterTriangle X Y φ n =
      ((OmegaSpectrum.signedLoopUnitStructurePath X n).basedPreAction
        (tracedSourceUnitStructureInput X Y φ n) (𝟙 A)).path := by
  rw [tracedSourceUnitParameterTriangle, ← Category.assoc,
    SSet.Edge.CompStruct.δ_two_yonedaEquiv_symm]
  change SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (OmegaSpectrum.signedLoopUnitStructurePath X n).path) ≫ _ = _
  rw [Equiv.symm_apply_apply, PointedMapping.VerticalPath.basedPreAction_action_path]
  rfl

/-- 第二辺は同じ前段の懸垂・構造像の区間の全パラメータ前合成。 -/
lemma tracedSourceUnitParameterTriangle_zero (n : ℕ) :
    stdSimplex.δ (0 : Fin 3) ≫ tracedSourceUnitParameterTriangle X Y φ n =
      ((OmegaSpectrum.tracedSignedLoopUnitStepInterval X n).basedPreAction
        (tracedSourceUnitStructureInput X Y φ n) (𝟙 A)).path := by
  rw [tracedSourceUnitParameterTriangle, ← Category.assoc,
    SSet.Edge.CompStruct.δ_zero_yonedaEquiv_symm]
  change SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (OmegaSpectrum.tracedSignedLoopUnitStepInterval X n).path) ≫ _ = _
  rw [Equiv.symm_apply_apply, PointedMapping.VerticalPath.basedPreAction_action_path]
  rfl

/-- 対角辺は次段延長を構造射へ制限した同じ区間の全パラメータ前合成。 -/
lemma tracedSourceUnitParameterTriangle_one (n : ℕ) :
    stdSimplex.δ (1 : Fin 3) ≫ tracedSourceUnitParameterTriangle X Y φ n =
      ((OmegaSpectrum.tracedSignedLoopUnitRestrictionInterval X n).basedPreAction
        (tracedSourceUnitStructureInput X Y φ n) (𝟙 A)).path := by
  rw [tracedSourceUnitParameterTriangle, ← Category.assoc,
    SSet.Edge.CompStruct.δ_one_yonedaEquiv_symm]
  change SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv (OmegaSpectrum.tracedSignedLoopUnitRestrictionInterval X n).path) ≫ _ = _
  rw [Equiv.symm_apply_apply, PointedMapping.VerticalPath.basedPreAction_action_path]
  rfl

end SerrePositivity.KST.Spectra.RawSpectrumMapping
