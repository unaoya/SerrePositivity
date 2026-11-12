module

public import SerrePositivity.KST.Spectra.CosimplicialLastVertex
public import SerrePositivity.KST.Spectra.TotalizationFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor

/-!
概要：通常の余単体 Tot から Bousfield–Kan homotopy Tot への標準比較射。
方針：終頂点の重みの射を普遍的な標準単体の族へ前合成し、end へ持ち上げる。
規約：射の構成と自然性には Reedy 条件を課さない。弱同値性は別途必要。
使われ方：Goerss–Jardine VII §4、VIII §1。Sp-4 の通常 Tot 比較。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet

open scoped MonoidalClosed

namespace SerrePositivity.KST.Spectra.CosimplicialTotalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 終頂点を普遍的な Tot の族へ代入した Bousfield–Kan 重みの族。 -/
def bousfieldKanFamily (X : CosimplicialObject SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} SimplexCategory) ⊗
      (Functor.const _).obj (obj X) ⟶ AsSmall.down ⋙ X where
  app j := (CosimplicialLastVertex.component j ▷ obj X) ≫
    MonoidalClosed.uncurry (π X (AsSmall.down.obj j))
  naturality i j f := by
    change (nerveMap (Over.map f) ▷ obj X) ≫ ((_ ▷ obj X) ≫ _) =
      ((_ ▷ obj X) ≫ _) ≫ X.map (AsSmall.down.map f)
    rw [← Category.assoc, ← comp_whiskerRight,
      CosimplicialLastVertex.naturality, comp_whiskerRight, Category.assoc]
    rw [Category.assoc]
    apply congrArg (fun t ↦ (CosimplicialLastVertex.component i ▷ obj X) ≫ t)
    rw [← uncurry_pre_app, ← uncurry_natural_right]
    exact congrArg MonoidalClosed.uncurry (condition X (AsSmall.down.map f)).symm

/-- 通常の Tot から同じ係数の Bousfield–Kan homotopy Tot への実際の比較射。 -/
def bousfieldKanComparison (X : CosimplicialObject SSet.{u}) :
    obj X ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim (AsSmall.down ⋙ X) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift (bousfieldKanFamily X)

@[reassoc]
lemma bousfieldKanComparison_π (X : CosimplicialObject SSet.{u})
    (j : AsSmall.{u} SimplexCategory) :
    bousfieldKanComparison X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _) (AsSmall.down ⋙ X) j =
    π X (AsSmall.down.obj j) ≫
      (pre (CosimplicialLastVertex.component j)).app (X.obj (AsSmall.down.obj j)) := by
  rw [bousfieldKanComparison, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_π]
  change curry ((CosimplicialLastVertex.component j ▷ obj X) ≫
    MonoidalClosed.uncurry (π X (AsSmall.down.obj j))) = _
  rw [← curry_pre_app, curry_uncurry]

/-- 比較射は係数の自然変換と厳密に可換。 -/
lemma bousfieldKanComparison_naturality {X Y : CosimplicialObject SSet.{u}}
    (f : X ⟶ Y) :
    map f ≫ bousfieldKanComparison Y = bousfieldKanComparison X ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight _) (Functor.whiskerLeft AsSmall.down f) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_hom_ext
  intro j
  conv_rhs => rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_π, ← Category.assoc,
    bousfieldKanComparison_π]
  rw [Category.assoc, bousfieldKanComparison_π, ← Category.assoc, map_π,
    Category.assoc]
  erw [← pre_comm_ihom_map]
  rw [Category.assoc]
  rfl

end
end SerrePositivity.KST.Spectra.CosimplicialTotalization
