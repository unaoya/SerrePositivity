module

public import SerrePositivity.KST.Spectra.TrivialFixedPointMapping
public import SerrePositivity.KST.Spectra.PointedSkeletalMappingTower

/-!
概要：自明作用の hG の各段を BG の骨格からの点つき Kan 写像空間の塔で表示する。
方針：定値 end の同型と骨格の写像空間の極限同型を合成する。
規約：各遷移は Kan fibration。π_* と極限の交換と有理 Shapiro はまだ主張しない。
使われ方：Goerss–Jardine VIII §§1–2、BF 1978 §2。有理 Shapiro の塔の解析。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet Opposite HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：自明作用の hG の段 k を計算する BG の骨格の塔。
方針：一対象群圏の nerve の骨格から段の係数への写像を取る。
規約：写像空間の基点は定数写像。群の有限性は不要。
使われ方：Goerss–Jardine VIII §§1–2。群 cochain と fiber の比較のための塔。 -/
def trivialFixedPointLevelTower (G : Type u) [Group G] (X : OmegaSpectrum.{u}) (k : ℕ) :
    ℕᵒᵖ ⥤ PointedSimplicialSet.{u} :=
  UnbasedPointedMapping.tower (nerve (AsSmall.{u} (SingleObj G))) (X.level k).space

instance trivialFixedPointLevelTower_kanComplex (G : Type u) [Group G]
    (X : OmegaSpectrum.{u}) (k : ℕ) (n : ℕᵒᵖ) :
    KanComplex ((trivialFixedPointLevelTower G X k).obj n).right :=
  UnbasedPointedMapping.tower_level_kanComplex _ _ n

/-- 概要：自明作用の hG の BG の骨格の塔の遷移は Kan fibration。
方針：骨格の単射から得た点つき写像空間の遷移の充填を使う。
規約：任意の二つの段の間の遷移を許す。
使われ方：Goerss–Jardine VIII §1。塔の fiber の長完全列。 -/
theorem trivialFixedPointLevelTower_fibration (G : Type u) [Group G]
    (X : OmegaSpectrum.{u}) (k : ℕ) {n m : ℕᵒᵖ} (f : n ⟶ m) :
    Fibration ((trivialFixedPointLevelTower G X k).map f).right :=
  UnbasedPointedMapping.tower_map_fibration _ _ f

/-- 概要：自明作用の置換前 hG の各段は BG の骨格の Kan 塔の極限と同型。
方針：点つき定値 end の比較と写像空間の骨格の塔からの復元を合成する。
規約：これは実際の通常の極限の同型でありホモトピー群の極限はまだ計算しない。
使われ方：Goerss–Jardine VIII §§1–2。塔の解析を構成済みの hG へ戻す界面。 -/
def trivialFixedPointLevelLimitIso (G : Type u) [Group G] (X : OmegaSpectrum.{u}) (k : ℕ) :
    ((homotopyFixedPointsKan (Action.trivial G X)).level k).space ≅
      limit (trivialFixedPointLevelTower G X k) :=
  trivialFixedPointLevelIso G X k ≪≫
    (UnbasedPointedMapping.coneIsLimit (nerve (AsSmall.{u} (SingleObj G)))
      (X.level k).space).conePointUniqueUpToIso
        (limit.isLimit (trivialFixedPointLevelTower G X k))

end

end SerrePositivity.KST.Spectra
