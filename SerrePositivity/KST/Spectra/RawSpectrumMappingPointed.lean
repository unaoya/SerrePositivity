module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingLaws

/-!
概要：整合写像空間に零写像の基点を入れ、点つきパラメータの普遍性を公開する。
方針：各段の内部 Hom の基点を整合族へ持ち上げ、評価で基点と普遍性を検査する。
規約：BF 源、任意の Kan 列を標的とする。使われ方：loop と写像空間の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping

/-- 段の境界比較は点つき射でもある。 -/
def pointedStep (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (n : ℕ) :
    PointedObject.basedHom (X.level n).space (Y.level n).space ⟶
      PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.level (n + 1)).space :=
  suspensionHom (X.level n).space (Y.level n).space ≫
    PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (Y.sigma n)

/-- 零写像を基点とする、元の整合写像空間。 -/
def pointedSpace (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) : PointedSimplicialSet.{u} :=
  Under.mk (lift X Y (fun n ↦ (PointedObject.basedHom (X.level n).space (Y.level n).space).hom)
    (fun n ↦ (Under.w (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space)).trans
      (Under.w (pointedStep X Y n)).symm))

/-- 基点を入れても元の Kan な整合写像単体集合を保つ。 -/
instance pointedSpace_kanComplex (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) :
    KanComplex (pointedSpace X Y).right := space_kanComplex X Y

/-- 各段評価は基点を保つ。 -/
def pointedEvaluation (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (n : ℕ) :
    pointedSpace X Y ⟶ PointedObject.basedHom (X.level n).space (Y.level n).space :=
  Under.homMk (evaluation X Y n) (lift_evaluation _ _ _ _ _)

@[reassoc]
lemma pointedEvaluation_condition (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) (n : ℕ) :
    pointedEvaluation X Y (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (Y.level (n + 1)).space =
      pointedEvaluation X Y n ≫ pointedStep X Y n := by
  apply Under.UnderMorphism.ext
  exact evaluation_condition X Y n

/-- 点つき整合族を元の点つき全写像空間へ持ち上げる。 -/
def pointedLift (X : OmegaSpectrum.{u}) (Y : KanSequence.{u}) {A : PointedSimplicialSet.{u}}
    (f : ∀ n, A ⟶ PointedObject.basedHom (X.level n).space (Y.level n).space)
    (hf : ∀ n, (f (n + 1)).right ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
      (f n).right ≫ step X Y n) : A ⟶ pointedSpace X Y :=
  Under.homMk (lift X Y (fun n ↦ (f n).right) hf) (by
    apply hom_ext X Y
    intro n
    rw [Category.assoc, lift_evaluation]
    exact (Under.w (f n)).trans (Under.w (pointedEvaluation X Y n)).symm)

@[reassoc (attr := simp)]
lemma pointedLift_evaluation (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    {A : PointedSimplicialSet.{u}}
    (f : ∀ n, A ⟶ PointedObject.basedHom (X.level n).space (Y.level n).space)
    (hf : ∀ n, (f (n + 1)).right ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre (X.sigma n) (Y.level (n + 1)).space =
      (f n).right ≫ step X Y n) (n : ℕ) :
    pointedLift X Y f hf ≫ pointedEvaluation X Y n = f n := by
  apply Under.UnderMorphism.ext
  exact lift_evaluation _ _ _ _ _

/-- 点つき全写像空間でも段の評価が射を決定する。 -/
lemma pointed_hom_ext (X : OmegaSpectrum.{u}) (Y : KanSequence.{u})
    {A : PointedSimplicialSet.{u}} {f g : A ⟶ pointedSpace X Y}
    (h : ∀ n, f ≫ pointedEvaluation X Y n = g ≫ pointedEvaluation X Y n) : f = g := by
  apply Under.UnderMorphism.ext
  exact hom_ext X Y (fun n ↦ congrArg Under.Hom.right (h n))

/-- 一般の Kan 列の射への後合成は零写像を保つ。 -/
def pointedPost (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}} (p : KanSequence.Hom Y Z) :
    pointedSpace X Y ⟶ pointedSpace X Z :=
  Under.homMk (post X p) (by
    apply hom_ext X Z
    intro n
    rw [Category.assoc, post_evaluation, ← Category.assoc]
    have he := Under.w (pointedEvaluation X Y n)
    change (pointedSpace X Y).hom ≫ evaluation X Y n = _ at he
    rw [he]
    exact (Under.w (PointedObject.basedHomMap (X.level n).space (p.app n))).trans
      (Under.w (pointedEvaluation X Z n)).symm)

@[reassoc (attr := simp)]
lemma pointedPost_evaluation (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}}
    (p : KanSequence.Hom Y Z) (n : ℕ) :
    pointedPost X p ≫ pointedEvaluation X Z n = pointedEvaluation X Y n ≫
      PointedObject.basedHomMap (X.level n).space (p.app n) := by
  apply Under.UnderMorphism.ext
  exact post_evaluation X p n

end SerrePositivity.KST.Spectra.RawSpectrumMapping
