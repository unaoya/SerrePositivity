module

public import SerrePositivity.KST.Spectra.RawSpectrumMappingLimitFamilies

/-!
概要：元の整合写像空間は、Kan 列の段ごとの点つき極限を保存する。
方針：構造条件を証明した各段の普遍族を全写像空間へ持ち上げ、射影で一意性を示す。
規約：任意のパラメータの単体を同時に扱う。使われ方：Hom と homotopy end の交換。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory Limits
namespace SerrePositivity.KST.Spectra.RawSpectrumMapping
variable {I : Type v} [Category.{w} I] {D : I ⥤ KanSequence.{u}}

/-- Hom の図式上の任意の錐から、元の全整合写像空間への厳密な普遍射。 -/
def limitLift (X : OmegaSpectrum.{u}) (c : Cone D)
    (hc : ∀ n, IsLimit ((KanSequence.levelEvaluation n).mapCone c))
    (s : Cone (D ⋙ pointedFunctor X)) : s.pt ⟶ pointedSpace X c.pt :=
  pointedLift X c.pt (limitFamily X c hc s)
    (fun n ↦ congrArg Under.Hom.right (limitFamily_condition X c hc s n))

@[reassoc (attr := simp)]
lemma limitLift_evaluation (X : OmegaSpectrum.{u}) (c : Cone D)
    (hc : ∀ n, IsLimit ((KanSequence.levelEvaluation n).mapCone c))
    (s : Cone (D ⋙ pointedFunctor X)) (n : ℕ) :
    limitLift X c hc s ≫ pointedEvaluation X c.pt n = limitFamily X c hc s n :=
  pointedLift_evaluation _ _ _ _ n

/-- 点つき Hom 関手は、指定した各段の極限錐を実際の極限錐へ送る。 -/
def isLimitOfLevelLimits (X : OmegaSpectrum.{u}) (c : Cone D)
    (hc : ∀ n, IsLimit ((KanSequence.levelEvaluation n).mapCone c)) :
    IsLimit ((pointedFunctor X).mapCone c) where
  lift := limitLift X c hc
  fac s i := by
    apply pointed_hom_ext X (D.obj i)
    intro n
    change (limitLift X c hc s ≫ pointedPost X (c.π.app i)) ≫
        pointedEvaluation X (D.obj i) n = s.π.app i ≫ pointedEvaluation X (D.obj i) n
    rw [Category.assoc, pointedPost_evaluation, ← Category.assoc, limitLift_evaluation]
    exact limitFamily_fac X c hc s n i
  uniq s m hm := by
    apply pointed_hom_ext X c.pt
    intro n
    rw [limitLift_evaluation]
    apply (levelHomCone_isLimit (X.level n).space c n (hc n)).hom_ext
    intro i
    change (m ≫ pointedEvaluation X c.pt n) ≫
        PointedObject.basedHomMap (X.level n).space ((c.π.app i).app n) =
      limitFamily X c hc s n ≫
        PointedObject.basedHomMap (X.level n).space ((c.π.app i).app n)
    have h := congrArg (fun p ↦ p ≫ pointedEvaluation X (D.obj i) n) (hm i)
    change (m ≫ pointedPost X (c.π.app i)) ≫ pointedEvaluation X (D.obj i) n = _ at h
    rw [Category.assoc, pointedPost_evaluation, ← Category.assoc] at h
    exact h.trans (limitFamily_fac X c hc s n i).symm

end SerrePositivity.KST.Spectra.RawSpectrumMapping
