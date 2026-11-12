module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleOutputResolutionHomotopy
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSemifreeDerivedHomInfinity
/-!
概要：固定入力ごとの D(R) 値 Hom の augmentation を、全単体上の自然な比較にする。
方針：実出力比較のホモトピーを元の半自由入力へ制限し、反変側は実反対 nerve を経由する。
規約：値域は全 R 加群の生の dg nerve。ここで準同型を可逆と主張しない。
使われ方：空間値 Hom との自然な比較に用いる、実 augmentation の関手族。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]
/-- 同じ入力宇宙で扱う、全 dg R 加群の実 nerve。 -/
abbrev dgHomModuleNerve (_D : Type v) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{u + 1, max (u + 1) v} (RightModule R PUnit.{1}))
/-- 実 D(R) の半自由模型から、全 dg R 加群への実包含。 -/
def dgHomModuleInclusionInfinity : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomDerivedNerve R D ⟶ dgHomModuleNerve R D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputInclusionLift.{u, max (u + 1) v, 0} R PUnit.{1})
/-- 固定始域の、元の同じ全 Hom の実 R 加群値 ∞ 関手。 -/
def dgSemifreeHomTargetModuleInfinity (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D ⟶ dgHomModuleNerve R D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetModuleDG R D P).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})))
/-- 固定終域の、dg 反対模型からの同じ全 Hom の実 R 加群値 ∞ 関手。 -/
def dgSemifreeHomSourceModuleInfinity (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ ⟶ dgHomModuleNerve R D :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomSourceModuleDG R D Q).comp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, u + 1, max (u + 1) v} R (RightModule R PUnit.{1})))
/-- 共変 D(R) 値 Hom の包含から元の Hom への、全単体上の実 augmentation。 -/
def dgSemifreeDerivedHomTargetAugmentationInfinity (P : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomTargetInfinity R D P ≫
      dgHomModuleInclusionInfinity R D) (dgSemifreeHomTargetModuleInfinity R D P) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) PUnit.{1}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetModuleDG R D P))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)))
  have h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputOriginalLift R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) PUnit.{1}
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomTargetModuleDG R D P)) =
      dgSemifreeHomTargetModuleInfinity R D P := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputOriginalLift_up]
    rfl
  exact { h := H.h
          h₀ := H.h₀.trans (Category.assoc _ _ _).symm
          h₁ := H.h₁.trans h1
          rel := H.rel }
/-- dg 反対模型上の D(R) 値 Hom から元の Hom への、全単体上の実 augmentation。 -/
def dgSemifreeDerivedHomSourceAugmentationInfinity (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedHomSourceDGopInfinity R D Q ≫
      dgHomModuleInclusionInfinity R D) (dgSemifreeHomSourceModuleInfinity R D Q) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputResolutionHomotopy R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ PUnit.{1}
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomSourceModuleDG R D Q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ))
  have h1 : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, u + 1} R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputOriginalLift R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)ᵒᵖ PUnit.{1}
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeHomSourceModuleDG R D Q)) =
      dgSemifreeHomSourceModuleInfinity R D Q := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.dgNerve.map_comp, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleOutputOriginalLift_up]
    rfl
  exact { h := H.h
          h₀ := H.h₀.trans (Category.assoc _ _ _).symm
          h₁ := H.h₁.trans h1
          rel := H.rel }
/-- 実反対 ∞ 圏からの、元の同じ全 Hom の R 加群値 ∞ 関手。 -/
def dgSemifreeHomContravariantModuleInfinity (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleDerivedInfinityCategory R D).op ⟶ dgHomModuleNerve R D :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom ≫
    dgSemifreeHomSourceModuleInfinity R D Q
/-- 実反対 ∞ 圏上でも、同じ実 augmentation は全関手の間のホモトピー。 -/
def dgSemifreeDerivedHomContravariantAugmentationInfinity (Q : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D) :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeDerivedContravariantHomInfinity R D Q ≫
      dgHomModuleInclusionInfinity R D) (dgSemifreeHomContravariantModuleInfinity R D Q) := by
  let H := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp (dgSemifreeDerivedHomSourceAugmentationInfinity R D Q)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveOppositeIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.SemifreeDGModules R D)).hom
  exact { h := H.h
          h₀ := H.h₀.trans (Category.assoc _ _ _).symm
          h₁ := H.h₁
          rel := H.rel }
end SerrePositivity.InfinityCategories.Project.DerivedCategories
