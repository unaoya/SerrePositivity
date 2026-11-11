module

public import SerrePositivity.KST.LocalizingInvariants.LaxDifferenceUnitSquare
public import SerrePositivity.KST.LocalizingInvariants.FunctorSquareArrowFamily
public import SerrePositivity.KST.LocalizingInvariants.ArrowFamilyRoundTrip

/-!
概要：元の lax pullback 内で id ⇒ difference≫ρ の実ホモトピーを構成する。
方針：四辺を固定した正方形を時間付き矢印族にし、元の F2 の pullback に持ち上げる。
規約：随伴の普遍性は後続。使われ方：差の実随伴の指定単位。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)
  {v : E.obj ⟶ D.obj} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction q.hom v) (hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful v)

/-- 元の C・D ホモトピーと元の四辺を保持する lax pullback 内の円柱。 -/
def laxDifferenceUnitPrism : (laxCategory p q).obj ⊗ (Δ[1] : SSet.{u}) ⟶
    (laxCategory p q).obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift p.hom q.hom (laxDifferenceUnitCHomotopy p q v).h
    (laxDifferenceUnitDHomotopy p q v a).h
    (FunctorSquareArrowFamily.family (laxDifferenceUnitSquare p q a hv))
    (FunctorSquareArrowFamily.source _) (FunctorSquareArrowFamily.target _)

lemma laxDifferenceUnitPrism_fst : laxDifferenceUnitPrism p q a hv ≫ (laxFst p q).hom =
    (laxDifferenceUnitCHomotopy p q v).h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_fst ..

lemma laxDifferenceUnitPrism_snd : laxDifferenceUnitPrism p q a hv ≫ (laxSnd p q).hom =
    (laxDifferenceUnitDHomotopy p q v a).h := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_snd ..

lemma laxDifferenceUnitPrism_arrow : laxDifferenceUnitPrism p q a hv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p.hom q.hom =
      FunctorSquareArrowFamily.family (laxDifferenceUnitSquare p q a hv) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackLift_arrow ..

lemma laxDifferenceUnitPrism_zero : SSet.ι₀ ≫ laxDifferenceUnitPrism p q a hv =
    𝟙 (laxCategory p q).obj := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullback_hom_ext p.hom q.hom
  · rw [Category.assoc, laxDifferenceUnitPrism_arrow, FunctorSquareArrowFamily.zero,
      Category.id_comp]
    exact ZeroArrowFamily.ofHomotopy_eq_of_h (laxArrowHomotopy p q) _ rfl
  · change (SSet.ι₀ ≫ laxDifferenceUnitPrism p q a hv) ≫ (laxFst p q).hom = _
    rw [Category.assoc, laxDifferenceUnitPrism_fst,
      (laxDifferenceUnitCHomotopy p q v).h₀, Category.id_comp]
    rfl
  · change (SSet.ι₀ ≫ laxDifferenceUnitPrism p q a hv) ≫ (laxSnd p q).hom = _
    rw [Category.assoc, laxDifferenceUnitPrism_snd,
      (laxDifferenceUnitDHomotopy p q v a).h₀, Category.id_comp]
    rfl

lemma laxDifferenceUnitPrism_one : SSet.ι₁ ≫ laxDifferenceUnitPrism p q a hv =
    laxDifference p q ≫ laxDifferenceRho p q v := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullback_hom_ext p.hom q.hom
  · rw [Category.assoc, laxDifferenceUnitPrism_arrow, FunctorSquareArrowFamily.one]
    have ht : ZeroArrowFamily.ofHomotopy (laxDifferenceUnitTargetArrowHomotopy p q v) =
        ZeroArrowFamily.ofHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (laxArrowHomotopy p q)
          (laxDifference p q ≫ laxDifferenceRho p q v)) := rfl
    rw [ht, ZeroArrowFamily.ofHomotopy_precomp,
      ZeroArrowFamily.ofHomotopy_eq_of_h (laxArrowHomotopy p q) _ rfl]
  · change (SSet.ι₁ ≫ laxDifferenceUnitPrism p q a hv) ≫ (laxFst p q).hom = _
    rw [Category.assoc, laxDifferenceUnitPrism_fst, (laxDifferenceUnitCHomotopy p q v).h₁]
    rfl
  · change (SSet.ι₁ ≫ laxDifferenceUnitPrism p q a hv) ≫ (laxSnd p q).hom = _
    rw [Category.assoc, laxDifferenceUnitPrism_snd, (laxDifferenceUnitDHomotopy p q v a).h₁]
    rfl

/-- 元の lax pullback 内の、恒等関手から difference≫ρ への実ホモトピー。 -/
def laxDifferenceUnitHomotopy : SSet.Homotopy (𝟙 (laxCategory p q).obj)
    (laxDifference p q ≫ laxDifferenceRho p q v) where
  h := laxDifferenceUnitPrism p q a hv
  h₀ := laxDifferenceUnitPrism_zero p q a hv
  h₁ := laxDifferenceUnitPrism_one p q a hv
  rel := by ext n ⟨x, y⟩; exact x.property.elim

/-- 写像空間による随伴判定に渡す、元の二関手に対する指定単位候補。 -/
def laxDifferenceUnitHom : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 (laxCategory p q).obj)
    (laxDifference p q ≫ laxDifferenceRho p q v) :=
  Truncated.HomotopyCategory.homMk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (laxDifferenceUnitHomotopy p q a hv))

/-- 実単位候補の第二射影は、元の転置された D 成分の類そのもの。 -/
lemma laxDifferenceUnitHom_snd_arrow :
    Arrow.mk ((hoFunctor.map ((ihom (laxCategory p q).obj).map (laxSnd p q).hom)).toFunctor.map
      (laxDifferenceUnitHom p q a hv)) = Arrow.mk (laxDifferenceUnitD p q a) := by
  have h := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom (laxDifferenceUnitHomotopy p q a hv) (laxSnd p q).hom
  change Truncated.HomotopyCategory.homMk _ =
    (hoFunctor.map ((ihom (laxCategory p q).obj).map (laxSnd p q).hom)).toFunctor.map
      (laxDifferenceUnitHom p q a hv) at h
  calc
    _ = Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (laxDifferenceUnitHomotopy p q a hv) (laxSnd p q).hom))) :=
      (congrArg Arrow.mk h).symm
    _ = Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy (laxDifferenceUnitD p q a)))) := by
      apply Truncated.HomotopyCategory.congr_arrowMk_homMk
      change SSet.yonedaEquiv (curry (laxDifferenceUnitPrism p q a hv ≫ (laxSnd p q).hom)) = _
      rw [laxDifferenceUnitPrism_snd]
      rfl
    _ = _ := congrArg Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom (laxDifferenceUnitD p q a))

end SerrePositivity.KST.LocalizingInvariants
