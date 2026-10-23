module

public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationConeRestriction
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverIsomorphism
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorActionEvaluation
public import SerrePositivity.InfinityCategories.F1.Universe.RelativeOverPre
public import SerrePositivity.InfinityCategories.HomotopyLimits.WeightedStrictConeFamily

/-!
概要：元の底上の射による切断制限を、全空間の同型と宇宙持ち上げで移す。
方針：後合成との厳密な自然性と、相対関手空間の元の同型を使う。
規約：制限する元の射を保持する。底の quasicategory 性は要求しない。
使われ方：元の小さい Yoneda 全空間から pointed な全錐の制限への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 全錐の元の切断制限は、右因子包含を底上の射として前合成した射。 -/
lemma leftFibrationConeRestriction_eq_overPre {K E B : SSet.{u}} (p : E ⟶ B)
    {D : K ⟶ B} (c : JoinCone D) :
    leftFibrationConeRestriction p c = relativeFunctorOverPre p
      (Over.homMk (U := Over.mk D) (V := Over.mk c.val)
        (joinInr (Δ[0] : SSet.{u}) K) c.property) := by
  apply relativeFunctorUncurry_injective p D
  rw [leftFibrationConeRestriction, relativeFunctorUncurry_eqToHom p c.property]
  have hl := relativeFunctorUncurry_pre (𝟙 (relativeFunctorSpace p c.val))
    (joinInr (Δ[0] : SSet.{u}) K)
  have hr := relativeFunctorOverPre_uncurry p
    (Over.homMk (U := Over.mk D) (V := Over.mk c.val)
      (joinInr (Δ[0] : SSet.{u}) K) c.property) (𝟙 (relativeFunctorSpace p c.val))
  simpa only [Category.id_comp] using hl.trans hr.symm

/-- 底上の元の射による前合成と、標的の元の底上の射による後合成は可換。 -/
lemma relativeFunctorOverPre_post {E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
    (f : E ⟶ F) (hf : f ≫ q = p) {a b : Over B} (g : a ⟶ b) :
    relativeFunctorPost p q f hf b.hom ≫ relativeFunctorOverPre q g =
      relativeFunctorOverPre p g ≫ relativeFunctorPost p q f hf a.hom := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro m α
  apply ConcreteCategory.hom_ext
  intro x
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply,
    relativeFunctorOverPre_apply, relativeFunctorPost_apply]

/-- 全空間の底上の同型は、元の始域制限の同値性を保ち反映する。 -/
lemma relativeFunctorOverPre_isQCatEquivalence_iff_of_overIso
    {B : SSet.{u}} {p q : Over B} [LeftFibration p.hom] [LeftFibration q.hom]
    (e : p ≅ q) {a b : Over B} (g : a ⟶ b) :
    IsQCatEquivalence (relativeFunctorOverPre p.hom g) ↔
      IsQCatEquivalence (relativeFunctorOverPre q.hom g) := by
  let ea : relativeFunctorSpace p.hom a.hom ≅ relativeFunctorSpace q.hom a.hom :=
    (relativeFunctorOverPostFunctor a.hom).mapIso e
  let eb : relativeFunctorSpace p.hom b.hom ≅ relativeFunctorSpace q.hom b.hom :=
    (relativeFunctorOverPostFunctor b.hom).mapIso e
  have ha : IsQCatEquivalence (relativeFunctorPost p.hom q.hom e.hom.left e.hom.w a.hom) :=
    (qCatEquivalenceOfIso ea).isQCatEquivalence
  have hb : IsQCatEquivalence (relativeFunctorPost p.hom q.hom e.hom.left e.hom.w b.hom) :=
    (qCatEquivalenceOfIso eb).isQCatEquivalence
  constructor
  · intro h
    apply hb.cancel_left
    rw [relativeFunctorOverPre_post]
    exact h.comp ha
  · intro h
    apply ha.cancel_right
    rw [← relativeFunctorOverPre_post]
    exact hb.comp h

/-- 元の始域制限の同値性は、持ち上げた同じ底上の射の前合成へ移る。 -/
lemma relativeFunctorOverPre_isQCatEquivalence_ulift
    {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : Over B} (g : a ⟶ b)
    (h : IsQCatEquivalence (relativeFunctorOverPre p g)) :
    IsQCatEquivalence (relativeFunctorOverPre ((SSet.uliftFunctor.{v, u}).map p)
      (uliftOverMorphism g)) := by
  have ha : IsQCatEquivalence (uliftRelativeFunctorMap.{u, v} p a.hom) :=
    (qCatEquivalenceOfIso (uliftRelativeFunctorIso.{u, v} p a.hom)).isQCatEquivalence
  have hb : IsQCatEquivalence (uliftRelativeFunctorMap.{u, v} p b.hom) :=
    (qCatEquivalenceOfIso (uliftRelativeFunctorIso.{u, v} p b.hom)).isQCatEquivalence
  apply hb.cancel_left
  rw [← uliftRelativeFunctorMap_overPre]
  exact ((isQCatEquivalence_ulift_iff_of_kan (relativeFunctorOverPre p g)).mpr h).comp ha

end SerrePositivity.InfinityCategories.HomotopyLimits
