module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingFunctor
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
概要：段ごとの点つき極限から、一般の Kan 列への Hom の普遍的な整合族を作る。
方針：内部 Hom の極限保存と各段評価の自然性を使い、全パラメータの構造条件を検査する。
規約：標的の Ω 条件や構造射の単射性は不要。使われ方：Hom と homotopy end の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits MonoidalCategory MonoidalClosed
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable {I : Type v} [Category.{w} I] {D : I ⥤ KanSequence.{u}}

/-- 段ごとの極限錐へ点つき内部 Hom を施した極限錐。 -/
def levelHomCone_isLimit (A : PointedSimplicialSet.{u}) (c : Cone D) (n : ℕ)
    (hc : IsLimit ((KanSequence.levelEvaluation n).mapCone c)) :
    IsLimit ((PointedObject.basedHomFunctor A).mapCone
      ((KanSequence.levelEvaluation n).mapCone c)) := by
  have := (PointedSimplicialSet.smashHomAdjunction A).isRightAdjoint
  exact isLimitOfPreserves (PointedObject.basedHomFunctor A) hc

/-- Hom の錐を指定段の内部 Hom の錐へ送る。 -/
def parameterLevelCone (X : OmegaSpectrum.{u}) (n : ℕ) (s : Cone (D ⋙ pointedFunctor X)) :
    Cone (D ⋙ KanSequence.levelEvaluation n ⋙
      PointedObject.basedHomFunctor (X.level n).space) :=
  (Cone.postcompose (Functor.whiskerLeft D (pointedEvaluationTransformation X n))).obj s

/-- 点つき Hom の任意の錐から各段の Hom への普遍射。 -/
def limitFamily (X : OmegaSpectrum.{u}) (c : Cone D)
    (hc : ∀ n, IsLimit ((KanSequence.levelEvaluation n).mapCone c))
    (s : Cone (D ⋙ pointedFunctor X)) (n : ℕ) :
    s.pt ⟶ PointedObject.basedHom (X.level n).space (c.pt.level n).space :=
  (levelHomCone_isLimit (X.level n).space c n (hc n)).lift (parameterLevelCone X n s)

@[reassoc]
lemma limitFamily_fac (X : OmegaSpectrum.{u}) (c : Cone D)
    (hc : ∀ n, IsLimit ((KanSequence.levelEvaluation n).mapCone c))
    (s : Cone (D ⋙ pointedFunctor X)) (n : ℕ) (i : I) :
    limitFamily X c hc s n ≫ PointedObject.basedHomMap (X.level n).space ((c.π.app i).app n) =
      s.π.app i ≫ pointedEvaluation X (D.obj i) n :=
  (levelHomCone_isLimit (X.level n).space c n (hc n)).fac (parameterLevelCone X n s) i

/-- 段の構造比較の後合成の自然性は点つき射でも厳密。 -/
lemma pointedStep_post (X : OmegaSpectrum.{u}) {Y Z : KanSequence.{u}} (p : Y ⟶ Z) (n : ℕ) :
    pointedStep X Y n ≫ PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) (p.app (n + 1)) =
      PointedObject.basedHomMap (X.level n).space (p.app n) ≫ pointedStep X Z n := by
  apply Under.UnderMorphism.ext
  exact step_post X p n

/-- 各段の普遍射は元の全写像空間への厳密な整合族をなす。 -/
lemma limitFamily_condition (X : OmegaSpectrum.{u}) (c : Cone D)
    (hc : ∀ n, IsLimit ((KanSequence.levelEvaluation n).mapCone c))
    (s : Cone (D ⋙ pointedFunctor X)) (n : ℕ) :
    limitFamily X c hc s (n + 1) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (c.pt.level (n + 1)).space =
      limitFamily X c hc s n ≫ pointedStep X c.pt n := by
  apply (levelHomCone_isLimit (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) c (n + 1) (hc (n + 1))).hom_ext
  intro i
  change (limitFamily X c hc s (n + 1) ≫
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (c.pt.level (n + 1)).space) ≫
        PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) ((c.π.app i).app (n + 1)) =
    (limitFamily X c hc s n ≫ pointedStep X c.pt n) ≫
      PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) ((c.π.app i).app (n + 1))
  have hpre : PointedObject.basedHomMap (X.level (n + 1)).space
      ((c.π.app i).app (n + 1)) ≫
        _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) ((D.obj i).level (n + 1)).space =
      _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (X.sigma n) (c.pt.level (n + 1)).space ≫
        PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space)
          ((c.π.app i).app (n + 1)) := by
    simp only [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre]
    exact (MonoidalClosed.pre (X.sigma n)).naturality ((c.π.app i).app (n + 1))
  rw [Category.assoc, ← hpre, ← Category.assoc, limitFamily_fac]
  have hs : pointedStep X c.pt n ≫
      PointedObject.basedHomMap (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension (X.level n).space) ((c.π.app i).app (n + 1)) =
      PointedObject.basedHomMap (X.level n).space ((c.π.app i).app n) ≫
        pointedStep X (D.obj i) n := pointedStep_post X (c.π.app i) n
  conv_rhs => rw [Category.assoc, hs, ← Category.assoc, limitFamily_fac]
  simp only [Category.assoc]
  rw [pointedEvaluation_condition]

end SerrePositivity.KST.Spectra.RawSpectrumMapping
