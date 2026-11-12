module

public import SerrePositivity.KST.Spectra.SkeletalTowerMittagLeffler
public import SerrePositivity.KST.Spectra.RationalLevelNormalizedCochains

/-!
概要：有限群と有理化スペクトル各段の骨格の写像空間の塔の収束判定。
方針：既証の正規化群 cohomology の消滅を実際の fiber 微分の補正へ入力する。
規約：ここでは高次群の Mittag–Leffler 条件を得る。Shapiro の全射性は別工程。
使われ方：Goerss–Jardine VIII §2、BF 1978 §2。有理自明作用の塔の解析。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet Opposite

namespace SerrePositivity.KST.Spectra.RationalSkeletalTower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 骨格の fiber の補正に必要な、実際の有理化各段の cohomology の消滅。 -/
theorem correction_cohomology_isZero (X : OmegaSpectrum.{u}) (k : ℕ)
    (G : Type u) [Group G] [Finite G] (n r : ℕ) :
    IsZero ((NormalizedValueCochains.complex (nerve (AsSmall.{u} (SingleObj G)))
      (AddCommGrpCat.of (SkeletalCellAttachment.positiveAdditiveCoefficient
        ((OmegaSpectrum.rationalization X).level k).space n (r + 1)))).homology (n + 2)) := by
  exact RationalLevelNormalizedCochains.positive_cohomology_isZero X k G
    (n + 1 + (r + 1)) (n + 1)

/-- 有限群の nerve から有理化各段への骨格の写像空間の塔は高次群で Mittag–Leffler。 -/
theorem groupTower_isMittagLeffler (X : OmegaSpectrum.{u}) (k : ℕ)
    (G : Type u) [Group G] [Finite G] (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.IsMittagLeffler
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
        ((UnbasedPointedMapping.tower (nerve (AsSmall.{u} (SingleObj G)))
          ((OmegaSpectrum.rationalization X).level k).space).obj (op n)).right (r + 2)
        ((UnbasedPointedMapping.tower (nerve (AsSmall.{u} (SingleObj G)))
          ((OmegaSpectrum.rationalization X).level k).space).obj (op n)).basepoint)
      (fun n ↦ pointedGroupMap (r + 2)
        ((UnbasedPointedMapping.tower (nerve (AsSmall.{u} (SingleObj G)))
          ((OmegaSpectrum.rationalization X).level k).space).map
            (homOfLE (Nat.le_succ n)).op)) :=
  UnbasedPointedMapping.groupTower_isMittagLeffler_of_isZero _ _ r
    (fun n ↦ correction_cohomology_isZero X k G n r)

/-- 実際の有理骨格の塔の高次群の lim¹ の消滅。 -/
theorem limOne_subsingleton (X : OmegaSpectrum.{u}) (k : ℕ)
    (G : Type u) [Group G] [Finite G] (r : ℕ) :
    Subsingleton (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
        ((UnbasedPointedMapping.tower (nerve (AsSmall.{u} (SingleObj G)))
          ((OmegaSpectrum.rationalization X).level k).space).obj (op n)).right (r + 2)
        ((UnbasedPointedMapping.tower (nerve (AsSmall.{u} (SingleObj G)))
          ((OmegaSpectrum.rationalization X).level k).space).obj (op n)).basepoint)
      (fun n ↦ pointedGroupMap (r + 2)
        ((UnbasedPointedMapping.tower (nerve (AsSmall.{u} (SingleObj G)))
          ((OmegaSpectrum.rationalization X).level k).space).map
            (homOfLE (Nat.le_succ n)).op))) :=
  _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.subsingleton_of_mittagLeffler _ _ (groupTower_isMittagLeffler X k G r)

end
end SerrePositivity.KST.Spectra.RationalSkeletalTower
