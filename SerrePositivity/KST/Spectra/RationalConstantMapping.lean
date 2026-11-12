module

public import SerrePositivity.KST.Spectra.InitialMappingEvaluation
public import SerrePositivity.KST.Spectra.RationalInitialDetection

/-!
概要：有限群の nerve への定数写像は有理化各段の高次群で同型。
方針：H¹ と高次 cohomology の消滅を評価の単射性へ渡し、定数写像の分裂を使う。
規約：通常の写像空間の π_(r+2)。スペクトルの全整数次数への移送は別工程。
使われ方：Goerss–Jardine VIII §2、BF 1978 §2。有理 Shapiro の各段での計算。
-/

@[expose] public section
universe u
open CategoryTheory SSet

namespace SerrePositivity.KST.Spectra.RationalSkeletalTower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 有理化各段の高次群では、有限群の nerve からの写像類は定数写像から来る。 -/
theorem constant_groupMap_surjective (X : OmegaSpectrum.{u}) (k : ℕ)
    (G : Type u) [Group G] [Finite G] (r : ℕ) :
    let K := nerve (AsSmall.{u} (SingleObj G))
    let Y := ((OmegaSpectrum.rationalization X).level k).space
    Function.Surjective (pointedGroupMap (r + 1) (UnbasedPointedMapping.constant K Y)) := by
  let v := (GroupNerve.coordinatesEquiv G 0).symm (fun i ↦ Fin.elim0 i)
  exact UnbasedPointedMapping.constant_groupMap_surjective_of_isZero _ v _ r
    (first_cohomology_isZero X k G r) (fun n ↦ correction_cohomology_isZero X k G n r)

/-- 有理化各段の高次群での定数写像の全単射性。 -/
theorem constant_groupMap_bijective (X : OmegaSpectrum.{u}) (k : ℕ)
    (G : Type u) [Group G] [Finite G] (r : ℕ) :
    let K := nerve (AsSmall.{u} (SingleObj G))
    let Y := ((OmegaSpectrum.rationalization X).level k).space
    Function.Bijective (pointedGroupMap (r + 1) (UnbasedPointedMapping.constant K Y)) := by
  let v := (GroupNerve.coordinatesEquiv G 0).symm (fun i ↦ Fin.elim0 i)
  exact ⟨UnbasedPointedMapping.constant_groupMap_injective (SSet.const v) _ (r + 1),
    constant_groupMap_surjective X k G r⟩

/-- 実際の定数写像の誘導準同型を順写像とする、有理化各段の高次群の同型。 -/
def constantGroupEquiv (X : OmegaSpectrum.{u}) (k : ℕ)
    (G : Type u) [Group G] [Finite G] (r : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((OmegaSpectrum.rationalization X).level k).space.right (r + 1)
      ((OmegaSpectrum.rationalization X).level k).space.basepoint ≃*
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (UnbasedPointedMapping.obj (nerve (AsSmall.{u} (SingleObj G)))
        ((OmegaSpectrum.rationalization X).level k).space).right (r + 1)
      (UnbasedPointedMapping.obj (nerve (AsSmall.{u} (SingleObj G)))
        ((OmegaSpectrum.rationalization X).level k).space).basepoint :=
  MulEquiv.ofBijective (pointedGroupMap (r + 1)
    (UnbasedPointedMapping.constant (nerve (AsSmall.{u} (SingleObj G)))
      ((OmegaSpectrum.rationalization X).level k).space))
    (constant_groupMap_bijective X k G r)

end
end SerrePositivity.KST.Spectra.RationalSkeletalTower
