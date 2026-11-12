module
public import SerrePositivity.KST.SConstruction.KRelativeFamilyLifting
public import SerrePositivity.KST.SConstruction.PrescribedSequenceFamilyRectification

/-! # 元の補正列から先に選ぶ BF 境界とその相対延長
概要：境界の raw 写像を BF へ先に持ち上げ、同じ境界を保つ全パラメータの BF 族を構成する。
方針：空境界での持ち上げと、指定境界での持ち上げを順に使う。
規約：raw 射影と指定した BF 境界を厳密に保持する。
使われ方：元の K prism の互換な補正列からの BF 族の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.Limits SSet Spectra

/-- 任意の raw 族の BF 持ち上げを、同じ射影の等式と共に保存する。 -/
def kRawFamilyLiftData (X Y : StableModel.{u}) {T : SSet.{u}}
    (b : T ⟶ RawSpectrumMapping.space (kOmegaSpectrum X) (kKanSequence Y)) :
    {a : T ⟶ OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y) //
      a ≫ kRawMappingProjection X Y = b} := by
  let j : (⊥_ SSet.{u}) ⟶ T := initial.to T
  let a := initial.to (OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y))
  let L := kRelativeFamilyLiftData X Y j a b (by apply initial.hom_ext)
  exact ⟨L.val, L.property.2⟩

variable (X Y : StableModel.{u}) {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
  (f : ∀ n, U ⟶ (PointedObject.basedHom ((kOmegaSpectrum X).level n).space
    ((kKanSequence Y).level n).space).right)
  (H : ∀ n, SSet.Homotopy
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum X).sigma n)
      ((kKanSequence Y).level (n + 1)).space)
    (f n ≫ RawSpectrumMapping.step (kOmegaSpectrum X) (kKanSequence Y) n))
  (B : TracedSequenceBoundaryData (kOmegaSpectrum X) (kKanSequence Y) j f H)

/-- 境界補正列から先に構成した raw 境界の BF 持ち上げ。 -/
def kTracedBoundaryLiftData :=
  kRawFamilyLiftData X Y (tracedSequenceBoundaryMap _ _ j f H B)

/-- 指定した BF 境界と元の raw 射影を同時に保持する全パラメータの BF 族。 -/
def kTracedFamilyLiftData :=
  kRelativeFamilyLiftData X Y j (kTracedBoundaryLiftData X Y j f H B).val
    (prescribedSequenceFamilyRectification _ _ j f H B)
    ((kTracedBoundaryLiftData X Y j f H B).property.trans
      (prescribedSequenceFamilyRectification_boundary _ _ j f H B).symm)

/-- 全 BF 族は先に構成した同じ BF 境界を厳密に回収する。 -/
lemma kTracedFamilyLiftData_boundary :
    j ≫ (kTracedFamilyLiftData X Y j f H B).val =
      (kTracedBoundaryLiftData X Y j f H B).val :=
  (kTracedFamilyLiftData X Y j f H B).property.1

/-- 全 BF 族の raw 射影は、指定補正列を保つ同じ厳密化である。 -/
lemma kTracedFamilyLiftData_projection :
    (kTracedFamilyLiftData X Y j f H B).val ≫ kRawMappingProjection X Y =
      prescribedSequenceFamilyRectification _ _ j f H B :=
  (kTracedFamilyLiftData X Y j f H B).property.2

end SerrePositivity.KST.SConstruction
