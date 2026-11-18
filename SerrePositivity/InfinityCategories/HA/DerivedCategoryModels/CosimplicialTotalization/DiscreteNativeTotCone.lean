module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.StrictDerivedTotCone
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.DiscreteComplexComparison

/-!
概要：離散加群の元のstrict余単体図式に、同じ積Totのnative極限錐を置く。
方針：C06を各次数の零次複体への同じ埋め込みへ制限する。
規約：IS-W2 D05の証明分割、raw補助。D06の交代余面複体への頂点比較とD07の全族は別工程。
使われ方：HA 1.2.4、G10の離散加群入力の入口。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 同じ離散加群図式の全nerveを元の宇宙で扱う。 -/
def strictCosimplicialModuleNerve (M : CosimplicialObject (ModuleCat.{u} A)) :
    (SSet.uliftFunctor.{u+1,0}).obj (nerve SimplexCategory) ⟶ nerve (ModuleCat.{u} A) :=
  (nerveAsSmallIso.{0,u+1} SimplexCategory).hom ≫
    resizedNerveMap (AsSmall.down ⋙ M)

/-- 元の加群を同じ零次複体からD(A)へ送る。 -/
def discreteModuleSource : nerve (ModuleCat.{u} A) ⟶ derivedInfinityCategory A :=
  nerveMap (HomologicalComplex.single (ModuleCat.{u} A) (.up ℤ) 0) ≫
    _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A

/-- 同じ元の離散図式の全単体の厳密等式。 -/
theorem discreteDiagram_strict (M : CosimplicialObject (ModuleCat.{u} A)) :
    strictCosimplicialComplexNerve ((discreteDiagramFunctor A).obj M) ≫
      _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A =
    strictCosimplicialModuleNerve A M ≫ discreteModuleSource A := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 離散加群の元の図式の指定native極限錐。 -/
def rawCosimplicialModuleCone (M : CosimplicialObject (ModuleCat.{u} A)) :
    JoinCone (strictCosimplicialModuleNerve A M ≫ discreteModuleSource A) :=
  joinConeOfDiagramEq (discreteDiagram_strict A M)
    (strictDerivedTotCone ((discreteDiagramFunctor A).obj M))

/-- 同じ離散加群図式の指定錐はnative極限錐。 -/
theorem rawCosimplicialModuleCone_isLimit (M : CosimplicialObject (ModuleCat.{u} A)) :
    IsLimitCone (rawCosimplicialModuleCone A M) :=
  joinConeOfDiagramEq_isLimit _ _
    (strictDerivedTotCone_isLimit ((discreteDiagramFunctor A).obj M))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
