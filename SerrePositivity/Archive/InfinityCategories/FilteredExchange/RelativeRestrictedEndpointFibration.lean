module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorRestrictedEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorAnodyneRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful

/-!
概要：left anodyne な相対端点評価は、底の表示変更と引き戻しの後も充満忠実。
方針：元の制限の trivial Kan fibration と二つの同型を合成する。
規約：全底・係数は任意。使われ方：始点も動く prism 比較の自然性の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 同じ元の相対端点評価は、left anodyne な包含に沿って全境界を持ち上げる。 -/
lemma relativeFunctorRestrictedEndpoint_trivialKanFibration {A C E F B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (b : A ⟶ B) (j : C ⟶ A)
    (q : F ⟶ B) (a : C ⟶ F) (hj : j ≫ b = a ≫ q) (hi : leftAnodyneExtensions j) :
    TrivialKanFibration (relativeFunctorRestrictedEndpoint p b j q a hj) := by
  have h₀ := relativeFunctorPre_trivialKanFibration p b j hi
  have h₁ : TrivialKanFibration (eqToHom (congrArg (relativeFunctorSpace p) hj)) := inferInstance
  have h₂ : TrivialKanFibration (relativeFunctorBaseChangeIso p q a).inv := inferInstance
  exact ⟨trivialKanFibrations.comp_mem _ _ h₀.mem
    (trivialKanFibrations.comp_mem _ _ h₁.mem h₂.mem)⟩

end SerrePositivity.InfinityCategories.F2
