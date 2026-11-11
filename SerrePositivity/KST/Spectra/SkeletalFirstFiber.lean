module

public import SerrePositivity.KST.Spectra.NormalizedFirstCocycles
public import SerrePositivity.KST.Spectra.SkeletalPositiveAdditiveDifferential

/-!
概要：H¹ の消滅から骨格の最初の fiber 微分の核を消す。
方針：実際の係数微分の核を正規化一次 cocycle へ移し、零次微分の零性を使う。
規約：源の零単体は一つ。通常の cohomology の消滅を入力する。
使われ方：Goerss–Jardine VIII §2。有理写像空間の零骨格での検出。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- H¹ が零なら、実際の最初の係数微分の核は単位元のみ。 -/
theorem first_coefficient_cocycle_eq_one
    (K : SSet.{u}) [Subsingleton (K _⦋0⦌)]
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (r : ℕ)
    (hH : IsZero ((NormalizedValueCochains.complex K
      (AddCommGrpCat.of (positiveAdditiveCoefficient Y 0 r))).homology 1))
    (z : coefficientGroup K Y 0 (r + 1))
    (hz : coefficientDifferential K Y 0 r z = 1) : z = 1 := by
  let M := AddCommGrpCat.of (positiveAdditiveCoefficient Y 0 r)
  let za : K.nonDegenerate 1 → M := fun s ↦ Additive.ofMul (z s)
  have hzpos : positiveAdditiveCoefficientDifferential K Y 0 r za = 0 := by
    funext s
    change (coefficientIndexEquiv Y _).toAdditive
      (Additive.ofMul (coefficientDifferential K Y 0 r z s)) = 0
    rw [hz]
    exact map_zero _
  have hδ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M 1 za = 0 := by
    have hm : za ∈ (positiveAdditiveCoefficientDifferential K Y 0 r).ker := hzpos
    rw [positiveAdditiveCoefficientDifferential_ker] at hm
    exact hm
  have he := NormalizedValueCochains.first_cocycle_eq_zero K M hH za hδ
  funext s
  exact congrArg Additive.toMul (congrFun he s)

/-- H¹ が零なら、最初の実際の fiber 微分の cocycle は単位元。 -/
theorem first_stage_cocycle_eq_one
    (K : SSet.{u}) [Subsingleton (K _⦋0⦌)]
    (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (r : ℕ)
    (hH : IsZero ((NormalizedValueCochains.complex K
      (AddCommGrpCat.of (positiveAdditiveCoefficient Y 0 r))).homology 1))
    (z : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (UnbasedPointedMapping.stageFiber K Y 0).right (r + 1)
      (UnbasedPointedMapping.stageFiber K Y 0).basepoint)
    (hz : UnbasedPointedMapping.stageDifferential K Y 0 r z = 1) : z = 1 := by
  apply (stageFiberCoefficientEquiv K Y 0 (r + 1)).injective
  rw [map_one]
  apply first_coefficient_cocycle_eq_one K Y r hH
  rw [stageFiberCoefficientEquiv_differential, hz, map_one]

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
