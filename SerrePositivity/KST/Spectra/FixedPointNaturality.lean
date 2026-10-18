module

public import SerrePositivity.KST.Spectra.FixedPointUnit
public import SerrePositivity.KST.Spectra.SpectrumHomotopyLimitNaturality

/-!
概要：自明作用の homotopy fixed points への実際の単位の自然性。
方針：自明作用の厳密な射と定数錐の可換式を BF end の標準比較の自然性へ渡す。
規約：全整数次数の準同型は実際の BF 射から誘導される。
使われ方：HA §1.4.2、BF 1978 §2、HTT A.3.3。有理 Shapiro の標準比較の自然性。
-/

@[expose] public section

universe u

open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：元の BF 射は自明な群作用の間の厳密な同変射。
方針：自明作用の全ての射は恒等射であることを使う。
規約：群の有限性は不要。
使われ方：HA §1.4.2。hG の単位の自然性の入力。 -/
def trivialActionMap (G : Type u) [Group G] {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) :
    Action.trivial G X ⟶ Action.trivial G Y where
  hom := f
  comm _ := by
    change 𝟙 X ≫ f = f ≫ 𝟙 Y
    simp only [Category.id_comp, Category.comp_id]

/-- 概要：hG の実際の単位は元のスペクトルの射に対して各段の成分で自然。
方針：自明作用の定数錐の厳密な自然性を BF end の比較へ適用する。
規約：hG の射への作用も実際の BF 射を使う。
使われ方：HA §1.4.2、BF 1978 §2。自明作用の標準比較の各段での整合性。 -/
theorem homotopyFixedPointsUnit_natural_component (G : Type u) [Group G]
    {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (n : ℕ) :
    PointedMapping.componentOf (f.app n ≫ (homotopyFixedPointsUnit G Y).app n) =
      PointedMapping.componentOf ((homotopyFixedPointsUnit G X).app n ≫
        (homotopyFixedPointsMap (trivialActionMap G f)).app n) :=
  OmegaSpectrum.homotopyLimitConeComparison_natural_component
    (trivialActionCone G X) (trivialActionCone G Y) f
    (Functor.whiskerLeft AsSmall.down ((GroupAction.diagramFunctor G).map (trivialActionMap G f)))
    (fun _ ↦ by
      change f ≫ 𝟙 Y = 𝟙 X ≫ f
      simp only [Category.comp_id, Category.id_comp]) n

/-- 概要：hG の実際の単位は全整数次数の誘導準同型で自然。
方針：各段の成分での自然性をホモトピー不変性へ移す。
規約：有理性・有限性をこの自然性の主張には使わない。
使われ方：HA §1.4.2、BF 1978 §2。有理 Shapiro の比較の π_* の自然性。 -/
theorem homotopyFixedPointsUnit_natural (G : Type u) [Group G]
    {X Y : OmegaSpectrum.{u}} (f : X ⟶ Y) (j : ℤ) :
    OmegaSpectrum.homotopyMap (f ≫ homotopyFixedPointsUnit G Y) j =
      OmegaSpectrum.homotopyMap
        (homotopyFixedPointsUnit G X ≫ homotopyFixedPointsMap (trivialActionMap G f)) j :=
  OmegaSpectrum.homotopyMap_eq_of_levelComponent (X := X)
    (Y := homotopyFixedPoints (Action.trivial G Y))
    (f ≫ homotopyFixedPointsUnit G Y)
    (homotopyFixedPointsUnit G X ≫ homotopyFixedPointsMap (trivialActionMap G f))
    (homotopyFixedPointsUnit_natural_component G f) j

end

end SerrePositivity.KST.Spectra
