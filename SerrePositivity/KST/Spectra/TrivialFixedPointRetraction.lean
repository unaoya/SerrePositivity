module

public import SerrePositivity.KST.Spectra.TrivialFixedPointUnitMapping
public import SerrePositivity.KST.Spectra.ConstantMappingRetraction

/-!
概要：自明作用の hG への標準射は各段で左逆を持つ。
方針：BF 射影、BG の写像空間の同型、BG の唯一の対象での評価を合成する。
規約：有限性や有理性を使わず、正次数群の単射性までを得る。
使われ方：Goerss–Jardine VIII §2、BF 1978 §2。有理 Shapiro の単射性。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory SSet

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：自明作用の hG の各段から元の段への点での評価。
方針：置換前の BG の写像空間へ移して標準頂点で評価する。
規約：この段ごとの左逆がスペクトルの射であることは主張しない。
使われ方：Goerss–Jardine VIII §2。標準比較の群の単射性の確認。 -/
def trivialFixedPointLevelRetraction (G : Type u) [Group G] (X : OmegaSpectrum.{u}) (k : ℕ) :
    ((homotopyFixedPoints (Action.trivial G X)).level k).space ⟶ (X.level k).space :=
  (homotopyFixedPointsProjection (Action.trivial G X)).app k ≫
    (trivialFixedPointLevelIso G X k).hom ≫
      UnbasedPointedMapping.evaluation
        (SSet.const (X := 𝟙_ SSet.{u})
          (ComposableArrows.mk₀ (AsSmall.up.obj (SingleObj.star G)))) (X.level k).space

/-- 概要：自明作用の標準射の各段に評価の厳密な左逆がある。
方針：標準射が定数写像に移る式と定数写像の評価の等式を使う。
規約：群の有限性と係数の有理性は不要。
使われ方：Goerss–Jardine VIII §2。標準射の単射性。 -/
@[reassoc (attr := simp)]
theorem homotopyFixedPointsUnit_level_retraction (G : Type u) [Group G]
    (X : OmegaSpectrum.{u}) (k : ℕ) :
    (homotopyFixedPointsUnit G X).app k ≫ trivialFixedPointLevelRetraction G X k =
      𝟙 (X.level k).space := by
  dsimp only [trivialFixedPointLevelRetraction]
  let v : 𝟙_ SSet.{u} ⟶ nerve (AsSmall.{u} (SingleObj G)) :=
    SSet.const (ComposableArrows.mk₀ (AsSmall.up.obj (SingleObj.star G)))
  have h := congrArg (fun f : (X.level k).space ⟶
      UnbasedPointedMapping.obj (nerve (AsSmall.{u} (SingleObj G))) (X.level k).space ↦
        f ≫ UnbasedPointedMapping.evaluation v (X.level k).space)
    (homotopyFixedPointsUnit_mapping G X k)
  simpa only [Category.assoc, UnbasedPointedMapping.constant_evaluation] using h

/-- 概要：自明作用の標準射は各段の全正次数群で単射。
方針：評価の左逆の等式を通常の誘導群準同型へ送る。
規約：π_* 同型の全射性はここから主張しない。
使われ方：Goerss–Jardine VIII §2。有理 Shapiro の単射側の実証。 -/
theorem homotopyFixedPointsUnit_level_groupMap_injective (G : Type u) [Group G]
    (X : OmegaSpectrum.{u}) (k r : ℕ) :
    Function.Injective (pointedGroupMap
      (X := (X.level k).space)
      (Y := ((homotopyFixedPoints (Action.trivial G X)).level k).space) r
        ((homotopyFixedPointsUnit G X).app k)) := by
  apply Function.LeftInverse.injective
    (g := pointedGroupMap r (trivialFixedPointLevelRetraction G X k))
  intro a
  rw [← pointedGroupMap_comp, homotopyFixedPointsUnit_level_retraction, pointedGroupMap_id]

end

end SerrePositivity.KST.Spectra
