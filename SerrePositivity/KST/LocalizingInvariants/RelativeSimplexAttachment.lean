module

public import SerrePositivity.KST.LocalizingInvariants.RelativeFunctorCoreRestriction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.SimplexAttachmentFamilies
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.CoreTrivialFibration
public import SerrePositivity.KST.Fibration.WeakHomotopyAnodyneComparison

/-!
概要：同じ有限単体の前段と次辺への制限は、元の core 逆像内でも全境界を充填する。
方針：実貼合せ境界が全頂点を覆うことを証明し、全相対図式の制限射に戻す。
規約：局所化後の商比較の充満忠実性とは別の制限射の RLP である。
使われ方：c5 の全図式と指定部分族の分母条件を保つ貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.Fibration SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.LocalizingInvariants

/-- 前段と次辺の元の貼合せ境界は、全頂点を厳密に覆う。 -/
lemma simplexAttachmentBoundary_vertexSurjective (n : ℕ) :
    Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary.{u} n).ι.app (Opposite.op ⦋0⦌)) := by
  intro v
  have hc : (∃ a, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌) a = v) ∨
      ∃ b, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌) b = v := by
    rcases v with ⟨ℓ, a, b⟩
    fin_cases ℓ
    · right
      cases a
      exact ⟨b, rfl⟩
    · left
      cases b
      exact ⟨a, rfl⟩
  rcases hc with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · exact ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix n).app (Opposite.op ⦋0⦌) a,
      ConcreteCategory.congr_hom (C := Type u)
        (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentPrefix_ι n) (Opposite.op ⦋0⦌)) a⟩
  · let w := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0]).app (Opposite.op ⦋0⦌) b
    refine ⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge n).app (Opposite.op ⦋0⦌) w, ?_⟩
    have he := ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentLastEdge_ι n) (Opposite.op ⦋0⦌)) w
    have hj : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[0] ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[n] : SSet.{u}) Δ[0] := by
      simpa only [Category.id_comp] using
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Quasicategory.simplexLastPoint n) (𝟙 (Δ[0] : SSet.{u}))
    exact he.trans (ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app hj (Opposite.op ⦋0⦌)) b)

/-- 同じ商の有限全図式を、同じ前段と次辺の貼合せ境界へ制限する実射。 -/
def relativeSimplexAttachmentRestriction {B C : SSet.{u}} [Quasicategory C]
    (q : B ⟶ C) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0]) : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n : SSet.{u}) : SSet.{u}) :=
  relativeFunctorCoreRestriction q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι
    (simplexAttachmentBoundary_vertexSurjective n)

/-- 同じ実貼合せ境界への制限の全単射 RLP は、元の相対図式内で成立する。 -/
instance relativeSimplexAttachmentRestriction_trivialKanFibration
    {B C : SSet.{u}} [Quasicategory B] [Quasicategory C] (q : B ⟶ C) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (relativeSimplexAttachmentRestriction q n) :=
  relativeFunctorCoreRestriction_trivialKanFibration _ _ _

/-- 指定部分族を全単体で固定し、同じ分母条件を持つ全図式の族を延長する。 -/
lemma exists_relative_simplexAttachmentCoreFamily
    {B C P Q : SSet.{u}} [Quasicategory B] [Quasicategory C]
    (q : B ⟶ C) (n : ℕ) (i : P ⟶ Q) [Mono i]
    (a : P ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0]) : SSet.{u}))
    (b : Q ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n : SSet.{u}) : SSet.{u}))
    (ha : a ≫ relativeSimplexAttachmentRestriction q n = i ≫ b) :
    ∃ F : Q ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0]) : SSet.{u}),
      i ≫ F = a ∧ F ≫ relativeSimplexAttachmentRestriction q n = b :=
  exists_relative_relativeFunctorCoreRestriction _ _ _ _ _ _ ha

/-- 元の全図式と貼合せ境界の商比較は、指定した同じ四辺で可換。 -/
lemma relativeSimplexAttachmentQuotient_square
    {B C : SSet.{u}} [Quasicategory C] (q : B ⟶ C) (n : ℕ) :
    relativeSimplexAttachmentRestriction q n ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n : SSet.{u}) =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0]) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app C) :=
  relativeFunctorCoreRestriction_quotient _ _ _

/-- c5 の全単体商比較の可逆性を、同じ貼合せ境界の商比較へ移す正確な同値。 -/
lemma relativeSimplexAttachmentQuotient_localized_isIso_iff
    {B C : SSet.{u}} [Quasicategory B] [Quasicategory C] (q : B ⟶ C) (n : ℕ) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0]))) ↔
    IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n : SSet.{u}))) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hs : IsIso (Q.map (relativeSimplexAttachmentRestriction q n)) :=
    homotopyEquivalence_anodyneQ_isIso _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence
  have ht : IsIso (Q.map
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app C))) := by
    have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app C)) :=
      _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.coreMap_trivialKanFibration _
    exact homotopyEquivalence_anodyneQ_isIso _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isSimplicialHomotopyEquivalence
  have he := congrArg Q.map (relativeSimplexAttachmentQuotient_square q n)
  rw [Q.map_comp, Q.map_comp] at he
  constructor
  · intro h
    have hc : IsIso (Q.map (relativeSimplexAttachmentRestriction q n) ≫
        Q.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n : SSet.{u}))) := by
      rw [he]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp hc
  · intro h
    have hc : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[n] : SSet.{u}) Δ[0])) ≫
        Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.simplexAttachmentBoundary n).ι).app C))) := by
      rw [← he]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp hc

end SerrePositivity.KST.LocalizingInvariants
