module

public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.StrictKanCommonWeightedComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorOverEquivalence
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition

/-!
概要：同じ共通 weighted 係数で検証した比較を、元の weighted nerve の全相対射へ戻す。
方針：実際の底上のパラメーター射による前合成同値を、相対関手空間と任意の族に適用する。
規約：追加パラメーターを点に制限せず、全体の関手同型を回収する。
使われ方：反転 unstraightening 比較の共同自然性を元の全相対 Hom 上へ降下する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories
open HomotopyLimits

variable {I : Type u} [SmallCategory I] (F : I ⥤ KanObject.{u})

/-- 元と共通解像の weighted nerve の間の、指定した同じパラメーター射を持つ底上の射。 -/
def strictKanCommonWeightedOverMap :
    Over.mk ((SSet.uliftFunctor.{u + 1, u}).map (weightedNerveProjection
      (simplicialHomDiagram (strictKanCommonDiagram F) edgewisePointKanObject ⋙
        SSet.opFunctor))) ⟶
    Over.mk ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (F ⋙ kanObjectForget))) :=
  Over.homMk (strictKanCommonWeightedParameterMap F)
    (strictKanCommonWeightedParameterMap_projection F)

/-- 同じパラメーター射への制限は、任意の同じ底上の left fibration への相対射の同値。 -/
lemma strictKanCommonWeightedOverPre_isQCatEquivalence
    {E : SSet.{u + 1}} (p : E ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve I))
    [LeftFibration p] :
    IsQCatEquivalence (relativeFunctorOverPre p (strictKanCommonWeightedOverMap F)) :=
  relativeFunctorOverPre_isQCatEquivalence p (strictKanCommonWeightedOverMap F)
    (strictKanCommonWeightedParameterMap_isPrecompositionEquivalence F)

/-- 共通係数への制限後の任意の族の同型は、元の全相対射の族の同型へ戻せる。 -/
def strictKanCommonWeightedDescendIso
    {E K : SSet.{u + 1}} (p : E ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (nerve I))
    [LeftFibration p]
    {f g : K ⟶ relativeFunctorSpace p ((SSet.uliftFunctor.{u + 1, u}).map
      (weightedNerveProjection (F ⋙ kanObjectForget)))}
    (e : FunctorIso (f ≫ relativeFunctorOverPre p (strictKanCommonWeightedOverMap F))
      (g ≫ relativeFunctorOverPre p (strictKanCommonWeightedOverMap F))) : FunctorIso f g :=
  (strictKanCommonWeightedOverPre_isQCatEquivalence F p).isFullyFaithful.preimageFunctorIso e

end SerrePositivity.InfinityCategories
