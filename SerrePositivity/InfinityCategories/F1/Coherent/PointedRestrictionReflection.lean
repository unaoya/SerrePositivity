module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentPointedRestriction

/-!
概要：元の coherent 図式の pointed な切断制限の同値性を、小さい全空間の制限へ反映する。
方針：底変換・縮小同型・宇宙持ち上げの可換四角形の同値性を逆向きに消去する。
規約：元の底上の制限射を保持し、一般の底の quasicategory 性は要求しない。
使われ方：全表現可能関手による極限の検出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

/-- 同じ pointed 制限の同値性は元の小さい全空間の制限に反映される。 -/
lemma relativeRestriction_isQCatEquivalence_of_coherentPointed {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    {a b : Over B} (g : a ⟶ b)
    (h : IsQCatEquivalence (coherentPointedRestriction F g)) :
    IsQCatEquivalence (relativeFunctorOverPre (smallLeftUnstraighteningProjection F) g) := by
  have : LeftFibration (Over.mk ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection F))).hom :=
    inferInstanceAs (LeftFibration ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection F)))
  have : LeftFibration (Over.mk (leftUnstraighteningProjection F)).hom :=
    inferInstanceAs (LeftFibration (leftUnstraighteningProjection F))
  have ha : IsQCatEquivalence (relativeFunctorBaseChangeForward pointedSpaceProjection F
      ((SSet.uliftFunctor.{u + 1, u}).map a.hom)) :=
    (qCatEquivalenceOfIso (relativeFunctorBaseChangeIso pointedSpaceProjection F
      ((SSet.uliftFunctor.{u + 1, u}).map a.hom))).isQCatEquivalence
  have hb : IsQCatEquivalence (relativeFunctorBaseChangeForward pointedSpaceProjection F
      ((SSet.uliftFunctor.{u + 1, u}).map b.hom)) :=
    (qCatEquivalenceOfIso (relativeFunctorBaseChangeIso pointedSpaceProjection F
      ((SSet.uliftFunctor.{u + 1, u}).map b.hom))).isQCatEquivalence
  have hl : IsQCatEquivalence
      (relativeFunctorOverPre (leftUnstraighteningProjection F) (uliftOverMorphism g)) := by
    apply ha.cancel_right
    have hn := relativeFunctorBaseChangeForward_overPre pointedSpaceProjection F (uliftOverMorphism g)
    exact hn.symm ▸ hb.comp h
  have hu := (relativeFunctorOverPre_isQCatEquivalence_iff_of_overIso
    (smallLeftUnstraighteningOverIso F) (uliftOverMorphism g)).mpr hl
  exact relativeFunctorOverPre_isQCatEquivalence_of_ulift
    (smallLeftUnstraighteningProjection F) g hu

end SerrePositivity.InfinityCategories
