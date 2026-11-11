module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGStableHomotopyNaturality
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleResolvedSourceSection
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleOutputResolutionClassical
/-!
概要：実入力切断の通常の h 上の作用を、同じ入力射影の H⁰ 同値の逆へ比較する。
方針：厳密切断の式と実 dg nerve の自然性から、全関手の比較同型を作る。
規約：指定済みの実切断を保つ。使われ方：実出力分解の主導来作用との照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (C : Type (max (u + 1) v)) [_root_.SerrePositivity.DifferentialGraded.DGCategory R C]
  (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 元の同じ実切断を、入力射影の H⁰ 比較同値の逆へ照合する。 -/
def dgModuleResolvedSourceSection_homotopyIso
    (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor R C (_root_.SerrePositivity.DifferentialGraded.RightModule R E)) :
    (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv)).toFunctor ⋙
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)).functor ≅
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R C).functor ⋙
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionSourceHomotopyEquivalence R C E F).inverse := by
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, max (u + 1) v, max (u + 1) v} R C) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSourceNerveEquivalence R C E F).inv
  let P := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleFunctorResolutionSource R C E F
  let hS := (hoFunctor.map S).toFunctor
  have hs : hS ⋙ (hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P)).toFunctor = 𝟭 _ := by
    change (hoFunctor.map S ≫ hoFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P)).toFunctor = _
    rw [← hoFunctor.map_comp]
    have e : S ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map P = 𝟙 _ :=
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolvedSourceSection_comp_source R C E F
    rw [e, hoFunctor.map_id]
    rfl
  have e : (hS ⋙
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleFunctorResolutionObject R C E F)).functor) ⋙
        P.onHomotopy ≅ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence R C).functor :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft hS (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgStableHomotopyEquivalence_naturalityIso R _ _ P).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (eqToIso hs) _ ≪≫ Functor.leftUnitor _
  exact CategoryTheory.Iso.isoCompInverse (H :=
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModuleResolutionSourceHomotopyEquivalence R C E F) e
end SerrePositivity.InfinityCategories.Project.DerivedCategories
