module
public import SerrePositivity.InfinityCategories.Stable.SpanHomotopyGluing
public import SerrePositivity.InfinityCategories.Derived.FunctorFamilyHomotopyUncurry
public import SerrePositivity.InfinityCategories.Derived.PinchedFamilyCompositionParameters
public import SerrePositivity.InfinityCategories.F1B.PinchedFamilyHomotopy
/-!
概要：三つの全選択空間上の評価同型から、全選択を同時に動かす実族の合成関係を得る。
方針：三同型を同じ二重パラメータ上の実ホモトピーへ戻し、実評価三角形の合成則を移す。
規約：三つの選択は独立に動かせる。使われ方：商 Hom 作用の全選択空間上の二入力整合性。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
/-- 三つの評価同型は、任意の共通選択パラメータ上の合成関係を与える。 -/
lemma pinchedFamilyComposition_evaluation {K X S₁ S₂ S₃ : SSet.{u}} [Quasicategory X]
    {x y z : X _⦋0⦌}
    (A₁ : S₁ ⟶ (ihom K).obj (pinchedHom x y))
    (A₂ : S₂ ⟶ (ihom K).obj (pinchedHom y z))
    (A₃ : S₃ ⟶ (ihom K).obj (pinchedHom x z))
    (f : K ⟶ pinchedHom x y) (g : K ⟶ pinchedHom y z) (c : K ⟶ pinchedHom x z)
    (I₁ : FunctorIso A₁ (SSet.const (functorVertex f)))
    (I₂ : FunctorIso A₂ (SSet.const (functorVertex g)))
    (I₃ : FunctorIso A₃ (SSet.const (functorVertex c)))
    (hc : intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y) ≫
      intervalFamilyHom (g ≫ pinchedHomToIntervalMappingSpace y z) =
        intervalFamilyHom (c ≫ pinchedHomToIntervalMappingSpace x z))
    (S : SSet.{u}) (p₁ : S ⟶ S₁) (p₂ : S ⟶ S₂) (p₃ : S ⟶ S₃) :
    intervalFamilyHom (uncurry (p₁ ≫ A₁) ≫ pinchedHomToIntervalMappingSpace x y) ≫
      intervalFamilyHom (uncurry (p₂ ≫ A₂) ≫ pinchedHomToIntervalMappingSpace y z) =
        intervalFamilyHom (uncurry (p₃ ≫ A₃) ≫ pinchedHomToIntervalMappingSpace x z) := by
  have h₁ : Nonempty (SSet.Homotopy (uncurry (p₁ ≫ A₁)) (fst K S ≫ f)) := by
    refine ⟨stableHomotopyRetarget (functorFamilyIsoUncurry (I₁.precomp p₁)) rfl ?_⟩
    rw [SSet.comp_const, uncurry_const_functorVertex]
  have h₂ : Nonempty (SSet.Homotopy (uncurry (p₂ ≫ A₂)) (fst K S ≫ g)) := by
    refine ⟨stableHomotopyRetarget (functorFamilyIsoUncurry (I₂.precomp p₂)) rfl ?_⟩
    rw [SSet.comp_const, uncurry_const_functorVertex]
  have h₃ : Nonempty (SSet.Homotopy (uncurry (p₃ ≫ A₃)) (fst K S ≫ c)) := by
    refine ⟨stableHomotopyRetarget (functorFamilyIsoUncurry (I₃.precomp p₃)) rfl ?_⟩
    rw [SSet.comp_const, uncurry_const_functorVertex]
  have e₁ := (pinchedFamilyHom_eq_iff_homotopy).mpr h₁
  have e₂ := (pinchedFamilyHom_eq_iff_homotopy).mpr h₂
  have e₃ := (pinchedFamilyHom_eq_iff_homotopy).mpr h₃
  exact (congrArg₂ (fun a b => a ≫ b) e₁ e₂).trans
    ((pinchedFamilyHom_comp_precomp (fst K S) f g c hc).trans e₃.symm)
end SerrePositivity.InfinityCategories
