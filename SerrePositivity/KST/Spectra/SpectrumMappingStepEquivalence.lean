module

public import SerrePositivity.InfinityCategories.Kan.Pointed.InternalHomTensorAdjointAction
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
        (InternalHomTensor.iso PointedSimplicialSet.circle.{u} (X.level n).space
          (Y.level (n + 1)).space).hom.right =
      (PointedObject.basedHomMap (X.level n).space
        (suspensionLoopEquiv (Y.level n).space (Y.level (n + 1)).space (Y.sigma n))).right := by
  change ((suspensionHom (X.level n).space (Y.level n).space ≫
      PointedObject.basedHomMap (suspension (X.level n).space) (Y.sigma n)) ≫
      (InternalHomTensor.iso PointedSimplicialSet.circle.{u} (X.level n).space
        (Y.level (n + 1)).space).hom).right = _
  apply congrArg Under.Hom.right
  exact
    (InternalHomExchange.tensorHom_adjoint PointedSimplicialSet.circle.{u}
      (X.level n).space (Y.level n).space (Y.level (n + 1)).space (Y.sigma n))

/-- 各段の構造比較は全基点 π 同型。 -/
lemma mappingStep_piIsomorphism (X Y : OmegaSpectrum.{u}) (n : ℕ) :
    KanPiIsomorphism (mappingStep X Y n) := by
  let e : (PointedObject.basedHom (suspension (X.level n).space)
      (Y.level (n + 1)).space).right ≅
      (PointedObject.basedHom (X.level n).space (loopSpace (Y.level (n + 1)).space)).right :=
    PointedSimplicialSet.forget.mapIso
    (InternalHomTensor.iso PointedSimplicialSet.circle.{u} (X.level n).space
      (Y.level (n + 1)).space)
  have he : KanPiIsomorphism e.hom := KanPiIsomorphism.of_iso
    (X := (PointedObject.basedHom (suspension (X.level n).space)
      (Y.level (n + 1)).space).right)
    (Y := (PointedObject.basedHom (X.level n).space
      (loopSpace (Y.level (n + 1)).space)).right) e
  have : KanComplex ((ihom PointedSimplicialSet.circle.{u}).obj
      (Y.level (n + 1)).space).right := PointedMapping.basedHom_kanComplex _ _
  have : KanComplex ((ihom (X.level n).space).obj
      ((ihom PointedSimplicialSet.circle.{u}).obj (Y.level (n + 1)).space)).right :=
    PointedMapping.basedHom_kanComplex _ _
  apply KanPiIsomorphism.of_comp (g := e.hom) _ he
  change KanPiIsomorphism (mappingStep X Y n ≫
    (InternalHomTensor.iso PointedSimplicialSet.circle.{u} (X.level n).space
      (Y.level (n + 1)).space).hom.right)
  rw [mappingStep_curry]
  exact PointedMapping.post_piIsomorphism _ _ (Y.omega_condition n)

end SerrePositivity.KST.Spectra.OmegaSpectrum
