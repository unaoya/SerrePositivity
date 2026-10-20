module
public import SerrePositivity.InfinityCategories.F1B.HomotopyWhiskering
public import SerrePositivity.InfinityCategories.Derived.RoofLeftPrismLift
public import SerrePositivity.InfinityCategories.Core.InitialUniqueness
/-!
概要：定値始点からの全パラメータの実ホモトピーを、同じ coslice 上の coherent な図式へ戻す。
方針：恒等錐から coslice の left fibration に沿って全区間を持ち上げる。
規約：同じ全底を持つ実 prism を保持する。使われ方：逆分母の右 Kan 形状への実現。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
/-- 定値始点からの実ホモトピーを、同じ全底・恒等始端を持つ coslice prism として表示する。 -/
structure CosliceHomotopyRealization {K X : SSet.{u}} (x : X _⦋0⦌) (f : K ⟶ X)
    (H : SSet.Homotopy (SSet.const x) f) where
  diagram : K ⟶ sliceUnder (SSet.yonedaEquiv.symm x)
  projection : diagram ≫ sliceUnderProjection _ = f
  prism : (Δ[1] : SSet.{u}) ⊗ K ⟶ sliceUnder (SSet.yonedaEquiv.symm x)
  start : prismEndpoint 0 K ≫ prism = SSet.const (cosliceIdentityCone x)
  finish : prismEndpoint 1 K ≫ prism = diagram
  base : prism ≫ sliceUnderProjection _ = (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h
/-- 任意 quasicategory の定値始点からの実ホモトピーに、同じ全添字の coslice 表示が存在する。 -/
lemma cosliceHomotopyRealization_nonempty {K X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) (f : K ⟶ X) (H : SSet.Homotopy (SSet.const x) f) :
    Nonempty (CosliceHomotopyRealization x f H) := by
  let p := sliceUnderProjection (SSet.yonedaEquiv.symm x)
  let a := SSet.const (X := K) (cosliceIdentityCone x)
  let γ := (β_ (Δ[1] : SSet.{u}) K).hom ≫ H.h
  have ha : a ≫ p = prismEndpoint 0 K ≫ γ := by
    change (SSet.const (cosliceIdentityCone x) ≫ sliceUnderProjection _) = _
    rw [SSet.const_comp, cosliceIdentityCone_projection]
    exact H.h₀.symm
  obtain ⟨J, h₀, hp⟩ := roofLeftFibration_lift_start_prism p a γ ha
  let c := prismEndpoint 1 K ≫ J
  have hc : c ≫ p = f := by
    dsimp only [c]
    rw [Category.assoc, hp]
    exact H.h₁
  exact ⟨⟨c, hc, J, h₀, rfl, hp⟩⟩
end SerrePositivity.InfinityCategories
