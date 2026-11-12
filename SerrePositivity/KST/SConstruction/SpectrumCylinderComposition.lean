module
public import SerrePositivity.KST.SConstruction.CompatibleFamilyComposition
public import SerrePositivity.KST.Spectra.RawSpectrumMapping

/-! # 厳密な BF 族と実補正円柱の合成の射影
概要：BF 族と任意の段の円柱の合成を、構造射の前合成と段の境界比較の下で計算する。
方針：BF 評価の厳密適合と一方の族だけの適合合成則を使う。
規約：独立な二つのパラメータと同じ全時刻の円柱を保持する。
使われ方：K の合成補正の後半 trace の計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
local instance spectrumCylinderCompositionPointedCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory
variable (X Y : OmegaSpectrum.{u}) {P Q : SSet.{u}}

/-- BF 族の段の評価と、独立な後続実円柱の合成。 -/
def spectrumCylinderComposite (Z : PointedSimplicialSet.{u}) (n : ℕ)
    (a : P ⟶ OmegaSpectrum.mappingSpace X Y)
    (h : Q ⊗ (Δ[1] : SSet.{u}) ⟶ (PointedObject.basedHom (Y.level n).space Z).right) :
    (P ⊗ Q) ⊗ (Δ[1] : SSet.{u}) ⟶ (PointedObject.basedHom (X.level n).space Z).right :=
  lift (fst (P ⊗ Q) Δ[1] ≫ fst P Q ≫ a ≫ OmegaSpectrum.evaluation X Y n)
    ((snd P Q ▷ (Δ[1] : SSet.{u})) ≫ h) ≫ eComp SSet (X.level n).space (Y.level n).space Z

/-- BF 族の段の suspension と、射影先の同じ後続実円柱の合成。 -/
def spectrumSuspendedCylinderComposite (Z : PointedSimplicialSet.{u}) (n : ℕ)
    (a : P ⟶ OmegaSpectrum.mappingSpace X Y)
    (h : Q ⊗ (Δ[1] : SSet.{u}) ⟶ (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (Y.level n).space) Z).right) :
    (P ⊗ Q) ⊗ (Δ[1] : SSet.{u}) ⟶
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) Z).right :=
  lift (fst (P ⊗ Q) Δ[1] ≫ fst P Q ≫ a ≫ OmegaSpectrum.evaluation X Y n ≫
      (suspensionHom (X.level n).space (Y.level n).space).right)
    ((snd P Q ▷ (Δ[1] : SSet.{u})) ≫ h) ≫
      eComp SSet (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (Y.level n).space) Z

/-- 厳密な BF 族との円柱合成の射影は、後続円柱の射影だけで計算できる。 -/
lemma spectrumCylinderComposite_projection (Z : PointedSimplicialSet.{u}) (n : ℕ)
    (a : P ⟶ OmegaSpectrum.mappingSpace X Y)
    (h : Q ⊗ (Δ[1] : SSet.{u}) ⟶ (PointedObject.basedHom (Y.level (n + 1)).space Z).right) :
    spectrumCylinderComposite X Y Z (n + 1) a h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) Z =
      spectrumSuspendedCylinderComposite X Y Z n a (h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (Y.sigma n) Z) := by
  unfold spectrumCylinderComposite spectrumSuspendedCylinderComposite
  simp only [← Category.assoc]
  apply pointed_left_compatible_lift
  simpa only [Category.assoc, OmegaSpectrum.mappingStep] using
    congrArg (fun q => (fst (P ⊗ Q) (Δ[1] : SSet.{u}) ≫ fst P Q ≫ a) ≫ q)
      (OmegaSpectrum.evaluation_condition X Y n)

/-- 後続円柱の段の境界比較は、合成円柱全体の同じ段の境界比較になる。 -/
lemma spectrumSuspendedCylinderComposite_step (Z : KanSequence.{u}) (n : ℕ)
    (a : P ⟶ OmegaSpectrum.mappingSpace X Y)
    (h : Q ⊗ (Δ[1] : SSet.{u}) ⟶
      (PointedObject.basedHom (Y.level n).space (Z.level n).space).right) :
    spectrumSuspendedCylinderComposite X Y (Z.level (n + 1)).space n a
        (h ≫ RawSpectrumMapping.step Y Z n) =
      spectrumCylinderComposite X Y (Z.level n).space n a h ≫ RawSpectrumMapping.step X Z n := by
  have hcomp := pointed_suspension_comp_lift (Z.sigma n)
    (fst (P ⊗ Q) (Δ[1] : SSet.{u}) ≫ fst P Q ≫ a ≫ OmegaSpectrum.evaluation X Y n)
    ((snd P Q ▷ (Δ[1] : SSet.{u})) ≫ h)
  simpa only [spectrumSuspendedCylinderComposite, spectrumCylinderComposite,
    RawSpectrumMapping.step, Category.assoc] using hcomp

end SerrePositivity.KST.SConstruction
