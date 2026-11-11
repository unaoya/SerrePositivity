module
public import SerrePositivity.KST.SConstruction.KRelativeFamilyLifting

/-! # 境界を保つ族の厳密化から実際の BF K 写像族へ
概要：適合円柱を持つ全段の族を、指定した BF 境界のまま実写像空間の族へ移す。
方針：相対逐次厳密化で未置換列への族を作り、元の単射置換の射影に沿って持ち上げる。
規約：適合円柱とその境界定数性を入力する。元の K の prism からの復号は後続工程。
使われ方：K の入力単体の境界を固定する、BF 写像空間への相対充填。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open Spectra
open scoped Simplicial
variable (X Y : StableModel.{u}) {T U : SSet.{u}} (j : T ⟶ U) [Mono j]
  (f : ∀ n, U ⟶ (PointedObject.basedHom ((kOmegaSpectrum X).level n).space
    ((kKanSequence Y).level n).space).right)
  (H : ∀ n, SSet.Homotopy
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum X).sigma n)
      ((kKanSequence Y).level (n + 1)).space)
    (f n ≫ RawSpectrumMapping.step (kOmegaSpectrum X) (kKanSequence Y) n))
  (hrel : ∀ n, (j ▷ (Δ[1] : SSet.{u})) ≫ (H n).h =
    fst T (Δ[1] : SSet.{u}) ≫ j ≫ f (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum X).sigma n) ((kKanSequence Y).level (n + 1)).space)
  (a : T ⟶ OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y))
  (ha : ∀ n, a ≫ OmegaSpectrum.evaluation (kOmegaSpectrum X) (kOmegaSpectrum Y) n ≫
    (PointedObject.basedHomMap ((kOmegaSpectrum X).level n).space
      ((monicKKanSequenceProjection Y).app n)).right = j ≫ f n)

/-- 全段の指定族を、元の BF 境界を厳密に保つ実写像族へ厳密化する。 -/
def relativeKFamilyRectificationData :
    {l : U ⟶ OmegaSpectrum.mappingSpace (kOmegaSpectrum X) (kOmegaSpectrum Y) //
      j ≫ l = a ∧ l ≫ kRawMappingProjection X Y =
        relativeSequenceFamilyRectification (kOmegaSpectrum X) (kKanSequence Y) j f H hrel} := by
  let b := relativeSequenceFamilyRectification (kOmegaSpectrum X) (kKanSequence Y) j f H hrel
  have hw : a ≫ kRawMappingProjection X Y = j ≫ b := by
    apply RawSpectrumMapping.hom_ext (kOmegaSpectrum X) (kKanSequence Y)
    intro n
    calc
      (a ≫ kRawMappingProjection X Y) ≫
          RawSpectrumMapping.evaluation (kOmegaSpectrum X) (kKanSequence Y) n =
        a ≫ OmegaSpectrum.evaluation (kOmegaSpectrum X) (kOmegaSpectrum Y) n ≫
          (PointedObject.basedHomMap ((kOmegaSpectrum X).level n).space
            ((monicKKanSequenceProjection Y).app n)).right := by
              rw [Category.assoc, kRawMappingProjection_evaluation]
      _ = j ≫ f n := ha n
      _ = (j ≫ b) ≫ RawSpectrumMapping.evaluation (kOmegaSpectrum X) (kKanSequence Y) n := by
        simpa only [Category.assoc] using
          (relativeSequenceFamilyRectification_boundary
            (kOmegaSpectrum X) (kKanSequence Y) j f H hrel n).symm
  exact kRelativeFamilyLiftData X Y j a b hw

/-- 構成した BF 写像族は元の指定境界を厳密に回収する。 -/
lemma relativeKFamilyRectificationData_boundary :
    j ≫ (relativeKFamilyRectificationData X Y j f H hrel a ha).val = a :=
  (relativeKFamilyRectificationData X Y j f H hrel a ha).property.1

/-- 構成した族の射影は、同じ全段の相対厳密化による族そのもの。 -/
lemma relativeKFamilyRectificationData_projection :
    (relativeKFamilyRectificationData X Y j f H hrel a ha).val ≫ kRawMappingProjection X Y =
      relativeSequenceFamilyRectification (kOmegaSpectrum X) (kKanSequence Y) j f H hrel :=
  (relativeKFamilyRectificationData X Y j f H hrel a ha).property.2

/-- 全段の射影した補正は、元の族と境界固定の実ホモトピーの有限列で結ばれる。 -/
lemma relativeKFamilyRectificationData_chain (n : ℕ) :
    Nonempty (RelativeFamilyChain j (f n)
      ((relativeKFamilyRectificationData X Y j f H hrel a ha).val ≫
        OmegaSpectrum.evaluation (kOmegaSpectrum X) (kOmegaSpectrum Y) n ≫
          (PointedObject.basedHomMap ((kOmegaSpectrum X).level n).space
            ((monicKKanSequenceProjection Y).app n)).right)) := by
  rw [← kRawMappingProjection_evaluation, ← Category.assoc,
    relativeKFamilyRectificationData_projection]
  exact relativeSequenceFamilyRectification_chain
    (kOmegaSpectrum X) (kKanSequence Y) j f H hrel n

end SerrePositivity.KST.SConstruction
