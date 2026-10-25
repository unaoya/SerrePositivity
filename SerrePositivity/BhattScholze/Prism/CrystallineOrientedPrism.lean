module

public import SerrePositivity.BhattScholze.Prism.OrientedPrism
public import SerrePositivity.BhattScholze.Delta.DeltaPrime

/-! # pを生成元に持つ結晶oriented prism

著者公開版Example 3.3。p正則・古典的p進完備なδ環から実導来条件を持つ
結晶prismを構成し、逆方向も共通比較で証明する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.OrientedPrism
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- p正則・p進完備なδ環に標準生成元pを持つ結晶oriented prismを付ける。 -/
def crystalline (D : DeltaStructure p A)
    (hp : Function.Injective (fun x : A ↦ (p : A) * x))
    [IsAdicComplete (Ideal.span {(p : A)}) A] : OrientedPrism p A :=
  ofDistinguished D (p : A)
    (D.isDistinguished_p (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)})
      (Ideal.subset_span (by simp)))) hp
    (DerivedCompletion.isModuleComplete_of_isAdicComplete A (p : A) (ModuleCat.of A A))
    (DerivedCompletion.isModuleComplete_of_isAdicComplete A (p : A) (ModuleCat.of A A))

/-- 結晶構成のδ構造は元の構造。 -/
@[simp] theorem crystalline_deltaStructure (D : DeltaStructure p A)
    (hp : Function.Injective (fun x : A ↦ (p : A) * x))
    [IsAdicComplete (Ideal.span {(p : A)}) A] : (crystalline D hp).deltaStructure = D := rfl

/-- 結晶構成の選択生成元はp。 -/
@[simp] theorem crystalline_generator (D : DeltaStructure p A)
    (hp : Function.Injective (fun x : A ↦ (p : A) * x))
    [IsAdicComplete (Ideal.span {(p : A)}) A] : (crystalline D hp).generator = (p : A) := rfl

/-- 指定δ構造と生成元pを持つ結晶oriented prismの存在条件は、p正則・p進完備性。
Example 3.3の両方向を実導来完備性と古典的完備性の比較により証明する。 -/
theorem exists_crystalline_iff (D : DeltaStructure p A) :
    (∃ P : OrientedPrism p A, P.deltaStructure = D ∧ P.generator = (p : A)) ↔
      Function.Injective (fun x : A ↦ (p : A) * x) ∧ IsAdicComplete (Ideal.span {(p : A)}) A := by
  constructor
  · rintro ⟨P, _, hgen⟩
    have hp : Function.Injective (fun x : A ↦ (p : A) * x) := by
      simpa only [hgen] using P.generator_regular
    exact ⟨hp, P.isAdicComplete_p_of_regular hp⟩
  · rintro ⟨hp, hc⟩
    let := hc
    exact ⟨crystalline D hp, rfl, rfl⟩

end SerrePositivity.BhattScholze.OrientedPrism
