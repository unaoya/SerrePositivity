module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SpanHomotopyGluing
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FunctorFamilyHomotopyUncurry
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.PinchedFamilyCompositionParameters
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.PinchedFamilyHomotopy
/-!
概要：三つの全選択空間上の評価同型から、全選択を同時に動かす実族の合成関係を得る。
方針：三同型を同じ二重パラメータ上の実ホモトピーへ戻し、実評価三角形の合成則を移す。
規約：三つの選択は独立に動かせる。使われ方：商 Hom 作用の全選択空間上の二入力整合性。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
/-- 三つの評価同型は、任意の共通選択パラメータ上の合成関係を与える。 -/
lemma pinchedFamilyComposition_evaluation {K X S₁ S₂ S₃ : SSet.{u}} [Quasicategory X]
    {x y z : X _⦋0⦌}
    (A₁ : S₁ ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y))
    (A₂ : S₂ ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y z))
    (A₃ : S₃ ⟶ (ihom K).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x z))
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y z) (c : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x z)
    (I₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso A₁ (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex f)))
    (I₂ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso A₂ (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex g)))
    (I₃ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso A₃ (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c)))
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace y z) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x z))
    (S : SSet.{u}) (p₁ : S ⟶ S₁) (p₂ : S ⟶ S₂) (p₃ : S ⟶ S₃) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (uncurry (p₁ ≫ A₁) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (uncurry (p₂ ≫ A₂) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace y z) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (uncurry (p₃ ≫ A₃) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x z) := by
  have h₁ : Nonempty (SSet.Homotopy (uncurry (p₁ ≫ A₁)) (fst K S ≫ f)) := by
    refine ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorFamilyIsoUncurry (I₁.precomp p₁)) rfl ?_⟩
    rw [SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  have h₂ : Nonempty (SSet.Homotopy (uncurry (p₂ ≫ A₂)) (fst K S ≫ g)) := by
    refine ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorFamilyIsoUncurry (I₂.precomp p₂)) rfl ?_⟩
    rw [SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  have h₃ : Nonempty (SSet.Homotopy (uncurry (p₃ ≫ A₃)) (fst K S ≫ c)) := by
    refine ⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableHomotopyRetarget (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.functorFamilyIsoUncurry (I₃.precomp p₃)) rfl ?_⟩
    rw [SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
  have e₁ := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilyHom_eq_iff_homotopy).mpr h₁
  have e₂ := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilyHom_eq_iff_homotopy).mpr h₂
  have e₃ := (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilyHom_eq_iff_homotopy).mpr h₃
  exact (congrArg₂ (fun a b => a ≫ b) e₁ e₂).trans
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.pinchedFamilyHom_comp_precomp (fst K S) f g c hc).trans e₃.symm)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
