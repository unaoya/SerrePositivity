module

public import SerrePositivity.EInfinity.PowerOperation.ComplexHammockFullyFaithful
public import SerrePositivity.EInfinity.PowerOperation.ComplexHammockEssentialSurjectivity
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneHammockFunctor

/-!
# 既存 D(A) から native な Sp への実 Eilenberg–Mac Lane 関手

DAG XIII §2.2 のスペクトル忘却。元の全複体の同じ hammock 比較を同値にし、
その逆を通して実スペクトル関手を降ろす。既存 D(A) の定義を変更しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories (derivedInfinityCategory)
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open FullFaithfulAndEssentiallySurjectiveFunctors
variable (A : Type u) [CommRing A]

/-- 指定 sourceIso を持つ元の全複体比較の、証明済みの全圏同値。 -/
def complexHammockDerivedEquivalence :
    QCatEquivalence (complexHammockNerve A) (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A) :=
  (isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (complexHammockDerivedComparison_fullyFaithful A)
    (complexHammockDerivedComparison_essentiallySurjective A)).choose

lemma complexHammockDerivedEquivalence_hom :
    (complexHammockDerivedEquivalence A).hom = complexHammockDerivedComparison A := rfl

/-- 元の複体の実スペクトルを既存 D(A) へ降ろした native な V_A。 -/
def eilenbergMacLaneDerived : _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory A ⟶ KST.Spectra.Sp.{u} :=
  (complexHammockDerivedEquivalence A).inv ≫ eilenbergMacLaneHammockFunctor A

/-- V_A は元の全複体の同じスペクトル図式へ、全関手の同型で戻る。 -/
def eilenbergMacLaneDerived_sourceIso :
    FunctorIso (complexRelativeDerivedSource A ≫ eilenbergMacLaneDerived A)
      (complexRelativeSpectrumSource A) := by
  let e := complexHammockDerivedEquivalence A
  let L := complexHammockSource A
  let H := eilenbergMacLaneHammockFunctor A
  have h₁ : FunctorIso (complexRelativeDerivedSource A ≫ eilenbergMacLaneDerived A)
      (L ≫ e.hom ≫ e.inv ≫ H) := by
    simpa only [e, L, H, eilenbergMacLaneDerived,
      complexHammockDerivedEquivalence_hom, Category.assoc] using
      FunctorIso.postcomp (complexHammockDerivedComparison_sourceIso A).symm
        (eilenbergMacLaneDerived A)
  have h₂ : FunctorIso (L ≫ e.hom ≫ e.inv ≫ H) (L ≫ H) := by
    simpa only [Category.assoc, Category.comp_id] using
      FunctorIso.postcomp (e.homInvIso.precomp L) H
  exact h₁.trans (h₂.trans (eilenbergMacLaneHammockFunctor_sourceIso A))

end SerrePositivity.EInfinity.PowerOperation
