module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FilteredInfinity
public import SerrePositivity.InfinityCategories.F1.CovariantRepresentableValues
public import SerrePositivity.InfinityCategories.Stable.UniverseLimits

/-!
概要：κ-compact 対象を、元の全共変 Hom 関手による小さい κ-filtered 余極限保存で定義。
方針：添字の宇宙と標的の宇宙を分け、指定された全余錐の像をそのまま使う。
規約：通常の圏上の図式や Hom 集合への置き換えは行わない。HTT 5.3.4。
使われ方：Yoneda 像の compact 性、有限余極限・retract 閉性、Ind の compact 部分。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact

/-- 元の全関手が、小さい κ-filtered 添字の指定された全余極限余錐を保存すること。 -/
def PreservesKappaFilteredColimits (κ : Cardinal.{u})
    {C : SSet.{max u v}} {Y : SSet.{max u v + 1}}
    (F : (SSet.uliftFunctor.{max u v + 1, max u v}).obj C ⟶ Y) : Prop :=
  ∀ (I : SSet.{u}) [Quasicategory I] [IsKappaFiltered κ I]
    (D : (SSet.uliftFunctor.{v, u}).obj I ⟶ C) (c : JoinCocone D),
    IsColimitCone c → IsColimitCone (mapJoinCocone F (JoinCocone.ulift c))

/-- 元の Map(x,−) が小さい κ-filtered 余極限を保つ、という κ-compact 性。 -/
def IsKappaCompact (κ : Cardinal.{u}) {C : SSet.{max u v}} [Quasicategory C]
    (x : C _⦋0⦌) : Prop :=
  PreservesKappaFilteredColimits.{u, v} κ (C := C) (covariantRepresentableInfinity x)

/-- compact は同じ全 Hom 関手についての ℵ₀-compact 性。 -/
abbrev IsCompact {C : SSet.{u}} [Quasicategory C] (x : C _⦋0⦌) : Prop :=
  IsKappaCompact.{u, u} Cardinal.aleph0 x

/-- κ-filtered 保存は、より大きい濃度の filtered 保存を含む。 -/
lemma PreservesKappaFilteredColimits.of_le {κ μ : Cardinal.{u}} (hκμ : κ ≤ μ)
    {C : SSet.{max u v}} {Y : SSet.{max u v + 1}}
    {F : (SSet.uliftFunctor.{max u v + 1, max u v}).obj C ⟶ Y}
    (h : PreservesKappaFilteredColimits.{u, v} κ F) :
    PreservesKappaFilteredColimits.{u, v} μ F := by
  intro I hI hFiltered D c hc
  have : IsKappaFiltered κ I := isKappaFiltered_of_le hκμ
  exact h I D c hc

/-- κ-compact 対象は κ ≤ μ のとき μ-compact。 -/
lemma IsKappaCompact.of_le {κ μ : Cardinal.{u}} (hκμ : κ ≤ μ)
    {C : SSet.{max u v}} [Quasicategory C] {x : C _⦋0⦌}
    (h : IsKappaCompact.{u, v} κ x) : IsKappaCompact.{u, v} μ x :=
  PreservesKappaFilteredColimits.of_le hκμ h

/-- ℵ₀-compact 性は、一般の小さい filtered ∞ 圏上の元の余錐で判定する。 -/
lemma isKappaCompact_aleph0_iff_filtered {C : SSet.{max u v}} [Quasicategory C] (x : C _⦋0⦌) :
    IsKappaCompact.{u, v} Cardinal.aleph0 x ↔
      ∀ (I : SSet.{u}) [Quasicategory I] [IsFilteredInfinity I]
        (D : (SSet.uliftFunctor.{v, u}).obj I ⟶ C) (c : JoinCocone D),
        IsColimitCone c → IsColimitCone
          (mapJoinCocone (covariantRepresentableInfinity x) (JoinCocone.ulift c)) := by
  constructor
  · intro h I hI hFiltered D c hc
    have : IsKappaFiltered Cardinal.aleph0 I := (isKappaFiltered_aleph0_iff I).mpr hFiltered
    exact h I D c hc
  · intro h I hI hFiltered D c hc
    have : IsFilteredInfinity I := (isKappaFiltered_aleph0_iff I).mp hFiltered
    exact h I D c hc

end SerrePositivity.InfinityCategories.F2.Compact
