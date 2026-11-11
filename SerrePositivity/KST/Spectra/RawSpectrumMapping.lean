module

public import SerrePositivity.KST.Spectra.TruncatedMappingUniversal
public import SerrePositivity.KST.Spectra.KanSequence
public import SerrePositivity.KST.Spectra.Limits.SpectrumMappingDiagram
public import SerrePositivity.KST.Spectra.TriangleMappingPost

/-!
概要：BF スペクトルを源、任意の Kan 列を標的とする整合写像空間。
方針：既存の切断 Hom の塔を、標的の単射構造の仮定なしで特殊化する。
規約：標的に Ω 条件も要求しない。使われ方：BF cotensor と homotopy end の写像空間の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- Kan 列を標的とする段の境界比較。 -/
def step (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (n : ℕ) :
    (PointedObject.basedHom (X.level n).space (Y.level n).space).right ⟶
      (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 1)).space).right :=
  (suspensionHom (X.level n).space (Y.level n).space).right ≫
    (PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.sigma n)).right

/-- 任意の Kan 列への厳密な整合写像族の単体集合。 -/
abbrev space (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) : SSet.{u} :=
  TruncatedMapping.total (fun n ↦ (X.level n).space) (fun n ↦ (Y.level n).space)
    (fun n ↦ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) X.sigma (step X Y)

/-- 整合写像空間は標的の構造射の単射性なしで Kan。 -/
instance space_kanComplex (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) :
    KanComplex (space X Y) := TruncatedMapping.total_kanComplex _ _ _ _ _

/-- 指定段への実際の評価。 -/
abbrev evaluation (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (n : ℕ) : space X Y ⟶
    (PointedObject.basedHom (X.level n).space (Y.level n).space).right :=
  TruncatedMapping.totalEvaluation _ _ _ _ _ n

@[reassoc]
lemma evaluation_condition (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (n : ℕ) :
    evaluation X Y (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
      evaluation X Y n ≫ step X Y n :=
  TruncatedMapping.totalEvaluation_condition _ _ _ _ _ n

/-- 段で整合するパラメータ族を実際の全写像空間へ持ち上げる。 -/
abbrev lift (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {A : SSet.{u}}
    (f : ∀ n, A ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right)
    (hf : ∀ n, f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
      f n ≫ step X Y n) : A ⟶ space X Y :=
  TruncatedMapping.familyLift _ _ _ _ _ f hf

@[reassoc (attr := simp)]
lemma lift_evaluation (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {A : SSet.{u}}
    (f : ∀ n, A ⟶ (PointedObject.basedHom (X.level n).space (Y.level n).space).right)
    (hf : ∀ n, f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
      f n ≫ step X Y n) (n : ℕ) : lift X Y f hf ≫ evaluation X Y n = f n :=
  TruncatedMapping.familyLift_evaluation _ _ _ _ _ f hf n

/-- 全ての段で一致する写像族は全写像空間でも等しい。 -/
lemma hom_ext (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {A : SSet.{u}}
    {f g : A ⟶ space X Y} (h : ∀ n, f ≫ evaluation X Y n = g ≫ evaluation X Y n) : f = g :=
  TruncatedMapping.total_hom_ext _ _ _ _ _ h

/-- Kan 列の射による後合成は段の境界比較と可換。 -/
lemma step_post (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}}
    (p : KanSequence.Hom Y Z) (n : ℕ) :
    step X Y n ≫ (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map (p.app (n + 1)) =
      (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor (X.level n).space).map (p.app n) ≫ step X Z n := by
  change ((suspensionHom (X.level n).space (Y.level n).space).right ≫
    (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map (Y.sigma n)) ≫ _ =
    _ ≫ (suspensionHom (X.level n).space (Z.level n).space).right ≫
      (_root_.SerrePositivity.InfinityCategories.HomotopyLimits.pointedMappingFunctor (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)).map (Z.sigma n)
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, ← p.comm,
    CategoryTheory.Functor.map_comp, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.HomotopyLimits.suspensionHom_post, Category.assoc]

/-- 実際の後合成の写像空間への射。 -/
def post (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}} (p : KanSequence.Hom Y Z) :
    space X Y ⟶ space X Z :=
  lift X Z (fun n ↦ evaluation X Y n ≫
    (PointedObject.basedHomMap (X.level n).space (p.app n)).right) (fun n ↦ by
      rw [Category.assoc, ← PointedMapping.pre_post_comm, ← Category.assoc,
        evaluation_condition, Category.assoc]
      exact congrArg (evaluation X Y n ≫ ·) (step_post X p n))

@[reassoc (attr := simp)]
lemma post_evaluation (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}}
    (p : KanSequence.Hom Y Z) (n : ℕ) :
    post X p ≫ evaluation X Z n = evaluation X Y n ≫
      (PointedObject.basedHomMap (X.level n).space (p.app n)).right :=
  lift_evaluation _ _ _ _ _

end SerrePositivity.KST.Spectra.RawSpectrumMapping
