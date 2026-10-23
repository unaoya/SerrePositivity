module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeRestrictionComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.SigmaYonedaConeSections
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallLeftUnstraighteningMappingSpace
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorBaseChangeNaturality

/-!
概要：小さい coherent 全空間の切断制限を、元の pointed space の持ち上げ制限へ移す。
方針：宇宙の相対 Hom 同型、元の縮小同型、元の pullback の底変換同型を順に使う。
規約：元の底上の射と全次数の制限作用を保持する。
使われ方：Yoneda 前層の元の極限錐の像を、空間値錐の切断で検査するための入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の coherent 図式に沿う pointed な持ち上げの、同じ底上の射による制限。 -/
def coherentPointedRestriction {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    {a b : Over B} (g : a ⟶ b) :
    relativeFunctorSpace pointedSpaceProjection ((SSet.uliftFunctor.{u + 1, u}).map b.hom ≫ F) ⟶
      relativeFunctorSpace pointedSpaceProjection ((SSet.uliftFunctor.{u + 1, u}).map a.hom ≫ F) :=
  relativeFunctorOverPre pointedSpaceProjection ((Over.map F).map (uliftOverMorphism g))

/-- 元の小さい全空間の同じ制限が同値なら、元の pointed 持ち上げの制限も同値。 -/
lemma coherentPointedRestriction_isQCatEquivalence {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
    {a b : Over B} (g : a ⟶ b)
    (h : IsQCatEquivalence (relativeFunctorOverPre (smallLeftUnstraighteningProjection F) g)) :
    IsQCatEquivalence (coherentPointedRestriction F g) := by
  have : LeftFibration (Over.mk ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection F))).hom :=
    inferInstanceAs (LeftFibration ((SSet.uliftFunctor.{u + 1, u}).map
      (smallLeftUnstraighteningProjection F)))
  have : LeftFibration (Over.mk (leftUnstraighteningProjection F)).hom :=
    inferInstanceAs (LeftFibration (leftUnstraighteningProjection F))
  have hu := relativeFunctorOverPre_isQCatEquivalence_ulift.{u, u + 1}
    (smallLeftUnstraighteningProjection F) g h
  have hl := (relativeFunctorOverPre_isQCatEquivalence_iff_of_overIso
    (smallLeftUnstraighteningOverIso F) (uliftOverMorphism g)).mp hu
  have ha : IsQCatEquivalence (relativeFunctorBaseChangeForward pointedSpaceProjection F
      ((SSet.uliftFunctor.{u + 1, u}).map a.hom)) :=
    (qCatEquivalenceOfIso (relativeFunctorBaseChangeIso pointedSpaceProjection F
      ((SSet.uliftFunctor.{u + 1, u}).map a.hom))).isQCatEquivalence
  have hb : IsQCatEquivalence (relativeFunctorBaseChangeForward pointedSpaceProjection F
      ((SSet.uliftFunctor.{u + 1, u}).map b.hom)) :=
    (qCatEquivalenceOfIso (relativeFunctorBaseChangeIso pointedSpaceProjection F
      ((SSet.uliftFunctor.{u + 1, u}).map b.hom))).isQCatEquivalence
  apply hb.cancel_left
  have hn := relativeFunctorBaseChangeForward_overPre pointedSpaceProjection F
    (uliftOverMorphism g)
  exact hn ▸ hl.comp ha

/-- 元の Yoneda 前層は、任意の元の極限錐の全 pointed 持ち上げの制限を同値にする。 -/
lemma representablePointedConeRestriction_isQCatEquivalence
    {K C : SSet.{u}} [Quasicategory C] {D : K ⟶ C.op}
    (c : JoinCone D) (hc : IsLimitCone c) (y : C _⦋0⦌) :
    IsQCatEquivalence (coherentPointedRestriction (representablePresheafInfinity y)
      (Over.homMk (U := Over.mk D) (V := Over.mk c.val)
        (joinInr (Δ[0] : SSet.{u}) K) c.property)) := by
  apply coherentPointedRestriction_isQCatEquivalence
  rw [← leftFibrationConeRestriction_eq_overPre]
  exact representableConeSectionRestriction_isQCatEquivalence c hc y

end SerrePositivity.InfinityCategories.HomotopyLimits
