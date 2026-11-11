module

public import SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensorAdjointAction
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism
public import SerrePositivity.KST.Spectra.OmegaSpectrum

/-!
概要：Ω スペクトルの構造射による写像空間の比較は全基点 π 同型。
方針：内部 Hom の curry 同型で Ω 随伴への後合成に同定する。
規約：源の有限性を要求しない。使われ方：一段移動の完全忠実性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 構造比較は curry 同型を通すと Ω 随伴への後合成である。 -/
lemma mappingStep_curry (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    mappingStep X Y n ≫
        (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u} (X.level n).space
          (Y.level (n + 1)).space).hom.right =
      (PointedObject.basedHomMap (X.level n).space
        (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspensionLoopEquiv (Y.level n).space (Y.level (n + 1)).space (Y.sigma n))).right := by
  change ((suspensionHom (X.level n).space (Y.level n).space ≫
      PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.sigma n)) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u} (X.level n).space
        (Y.level (n + 1)).space).hom).right = _
  apply congrArg Under.Hom.right
  exact
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.tensorHom_adjoint PointedSimplicialSet.circle.{u}
      (X.level n).space (Y.level n).space (Y.level (n + 1)).space (Y.sigma n))

/-- 各段の構造比較は全基点 π 同型。 -/
lemma mappingStep_piIsomorphism (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (mappingStep X Y n) := by
  let e : (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      (Y.level (n + 1)).space).right ≅
      (PointedObject.basedHom (X.level n).space (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (Y.level (n + 1)).space)).right :=
    PointedSimplicialSet.forget.mapIso
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u} (X.level n).space
      (Y.level (n + 1)).space)
  have he : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism e.hom := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanPiIsomorphism.of_iso
    (X := (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
      (Y.level (n + 1)).space).right)
    (Y := (PointedObject.basedHom (X.level n).space
      (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace (Y.level (n + 1)).space)).right) e
  have : KanComplex ((ihom PointedSimplicialSet.circle.{u}).obj
      (Y.level (n + 1)).space).right := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  have : KanComplex ((ihom (X.level n).space).obj
      ((ihom PointedSimplicialSet.circle.{u}).obj (Y.level (n + 1)).space)).right :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _
  apply _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism.of_comp (g := e.hom) _ he
  change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (mappingStep X Y n ≫
    (_root_.SerrePositivity.InfinityCategories.Project.PointedSpaces.InternalHomTensor.iso PointedSimplicialSet.circle.{u} (X.level n).space
      (Y.level (n + 1)).space).hom.right)
  rw [mappingStep_curry]
  exact PointedMapping.post_piIsomorphism _ _ (Y.omega_condition n)

end SerrePositivity.KST.Spectra.OmegaSpectrum
