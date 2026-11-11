module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SectionShapePushout
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：coherent cospan 上の切断空間を、二辺上の切断の厳密な引き戻しへ表示する。
方針：二辺の共通終点を底上の射として固定し、形状の押し出しの切断判定を適用する。
規約：元の図式と両辺への制限を保持。使われ方：native 切断族と模型 fiber 比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B : SSet.{u}} (p : E ⟶ B) (d : (horn 2 2 : SSet.{u}) ⟶ B)
local notation "l" => horn₂₂.ι₀₂ ≫ d
local notation "r" => horn₂₂.ι₁₂ ≫ d
local notation "t" => stdSimplex.δ (0 : Fin 2) ≫ l

/-- 左辺の終点を、同じ cospan の共通終点として底上に指定する。 -/
def relativeCospanLeftTarget : Over.mk t ⟶ Over.mk l :=
  Over.homMk (stdSimplex.δ (0 : Fin 2)) rfl

/-- 右辺の終点は左辺と同じ底の零単体を持つ。 -/
def relativeCospanRightTarget : Over.mk t ⟶ Over.mk r :=
  Over.homMk (stdSimplex.δ (0 : Fin 2)) (by
    change stdSimplex.δ (0 : Fin 2) ≫ (horn₂₂.ι₁₂ ≫ d) =
      stdSimplex.δ (0 : Fin 2) ≫ (horn₂₂.ι₀₂ ≫ d)
    simpa only [Category.assoc] using
      congrArg (fun k => k ≫ d) horn₂₂.isPushout.w.symm)

/-- 元の cospan の左辺の包含を底上で表示する。 -/
def relativeCospanLeftInclusion : Over.mk l ⟶ Over.mk d :=
  Over.homMk horn₂₂.ι₀₂ rfl

/-- 元の cospan の右辺の包含を底上で表示する。 -/
def relativeCospanRightInclusion : Over.mk r ⟶ Over.mk d :=
  Over.homMk horn₂₂.ι₁₂ rfl

/-- 二辺への実際の制限は、共通終点への制限の厳密な引き戻しをなす。 -/
lemma relativeCospanSections_isPullback :
    IsPullback (relativeFunctorPre p d horn₂₂.ι₀₂) (relativeFunctorPre p d horn₂₂.ι₁₂)
      (relativeFunctorOverPre p (relativeCospanLeftTarget d))
      (relativeFunctorOverPre p (relativeCospanRightTarget d)) :=
  HomotopyLimits.relativeFunctorOverPre_isPullback_of_pushout p
    (relativeCospanLeftTarget d) (relativeCospanRightTarget d)
    (relativeCospanLeftInclusion d) (relativeCospanRightInclusion d) horn₂₂.isPushout

/-- 二辺と共通終点の元の切断による、cospan 切断空間の厳密な表示。 -/
def relativeCospanSectionsIso : relativeFunctorSpace p d ≅
    pullback (relativeFunctorOverPre p (relativeCospanLeftTarget d))
      (relativeFunctorOverPre p (relativeCospanRightTarget d)) :=
  (relativeCospanSections_isPullback p d).isoPullback

/-- 表示同型の第一射影は元の左辺への制限そのもの。 -/
lemma relativeCospanSectionsIso_left :
    (relativeCospanSectionsIso p d).hom ≫ pullback.fst _ _ =
      relativeFunctorPre p d horn₂₂.ι₀₂ :=
  (relativeCospanSections_isPullback p d).isoPullback_hom_fst

/-- 表示同型の第二射影は元の右辺への制限そのもの。 -/
lemma relativeCospanSectionsIso_right :
    (relativeCospanSectionsIso p d).hom ≫ pullback.snd _ _ =
      relativeFunctorPre p d horn₂₂.ι₁₂ :=
  (relativeCospanSections_isPullback p d).isoPullback_hom_snd

end SerrePositivity.InfinityCategories.F2
