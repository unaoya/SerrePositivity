module

public import SerrePositivity.InfinityCategories.Sheaves.LargeSheafSmallModel
public import SerrePositivity.InfinityCategories.Sheaves.GlobalSectionsFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableEquivalence

/-!
概要：本質的小さい大きい site の元の全前層圏上で、大域切断の全右随伴を作る。
方針：小さい模型から同じ universe の presentable 性を移し、既存の随伴関手定理を用いる。
使われ方：HTT 5.5.2.9・6.2.2.6、Kerodon §7.1（Tag 02H1）の大域切断。
規約：係数を SSet(u+2) に上げず、元の定値関手の右随伴を結論する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type (u + 1)} [Category.{u} C] {D : Type u} [SmallCategory D]
variable {E : SSet.{u + 1}} [Quasicategory E]

/-- 同じ係数の大きい全前層圏の presentable 性を、小さい模型から回収する。 -/
lemma largePresheaf_isPresentable (e : D ≌ C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable
      (LargePresheafCat C E) :=
  (functor_isPresentable (nerve Dᵒᵖ) hE).of_equivalence
    (reindexSmallModelPresheafFunctor_isQCatEquivalence (E := E) e).choose.symm

/-- 元の大きい site の定値関手の右随伴は、同じ universe で存在する。 -/
lemma exists_largeGlobalSectionsFunctor (e : D ≌ C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    ∃ R : LargePresheafCat C E ⟶ E,
      Nonempty (QCatAdjunction (constantFunctorMap (nerve Cᵒᵖ) E) R) :=
  (exists_rightAdjoint_iff_preservesSmallColimits hE (largePresheaf_isPresentable e hE) _).mpr
    (constantFunctorMap_preservesSmallColimits _)

/-- 元の全前層の射と高次単体を同時に保持する、大きい site の大域切断。 -/
def largeGlobalSectionsFunctor (e : D ≌ C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    LargePresheafCat C E ⟶ E := Classical.choose (exists_largeGlobalSectionsFunctor e hE)

/-- 同じ大域切断の全関手と、元の定値関手の随伴データ。 -/
def largeGlobalSectionsAdjunction (e : D ≌ C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    QCatAdjunction (constantFunctorMap (nerve Cᵒᵖ) E) (largeGlobalSectionsFunctor e hE) :=
  Classical.choice (Classical.choose_spec (exists_largeGlobalSectionsFunctor e hE))

/-- 小さい模型は存在証明だけに使うため、選んだ元の大きい Γ 関手は模型に依存しない。 -/
lemma largeGlobalSectionsFunctor_eq {D' : Type u} [SmallCategory D'] (e : D ≌ C) (e' : D' ≌ C)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    largeGlobalSectionsFunctor e hE = largeGlobalSectionsFunctor e' hE := rfl

end SerrePositivity.InfinityCategories.Sheaves
