module

public import SerrePositivity.KST.Spectra.SkeletalPositiveAdditiveDifferential
public import SerrePositivity.KST.Spectra.NormalizedValueCochainExactness

/-!
概要：正規化 cohomology の消滅を実際の骨格の係数微分の完全性へ移す。
方針：核と像の既証の同定を使い、二つの添字表示を標準係数同型でそろえる。
規約：微分の符号は像を変えない。添字の同定も加法的な係数射として明示する。
使われ方：Goerss–Jardine VIII §§1–2。幾何的な障害を消す fiber の原像。
-/

@[expose] public section
universe u
open CategoryTheory Limits SSet

namespace SerrePositivity.KST.Spectra.SkeletalCellAttachment

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

set_option maxRecDepth 2048 in
-- fiber 係数の群と加法表示の別名を照合するため。
/-- cohomology の消滅の下で、係数微分の cocycle は直前の係数微分の像。 -/
theorem coefficientDifferential_exists_preimage_of_isZero
    (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) [KanComplex Y.right] (n r : ℕ)
    (hH : IsZero ((NormalizedValueCochains.complex K
      (AddCommGrpCat.of (positiveAdditiveCoefficient Y n (r + 1)))).homology (n + 2)))
    (z : coefficientGroup K Y (n + 1) (r + 1))
    (hz : coefficientDifferential K Y (n + 1) r z = 1) :
    ∃ c : coefficientGroup K Y n (r + 2), coefficientDifferential K Y n (r + 1) c = z := by
  let N := AddCommGrpCat.of (positiveAdditiveCoefficient Y (n + 1) r)
  let M := AddCommGrpCat.of (positiveAdditiveCoefficient Y n (r + 1))
  let e := (coefficientIndexEquiv Y
    (by omega : n + 1 + 1 + (r + 1) = n + 1 + (r + 1 + 1))).toAdditive
  let za : K.nonDegenerate (n + 2) → N := fun s ↦ Additive.ofMul (z s)
  have hzpos : positiveAdditiveCoefficientDifferential K Y (n + 1) r za = 0 := by
    funext s
    change (coefficientIndexEquiv Y _).toAdditive
      (Additive.ofMul (coefficientDifferential K Y (n + 1) r z s)) = 0
    rw [hz]
    exact map_zero _
  have hδ : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K N (n + 2) za = 0 := by
    have hm : za ∈ (positiveAdditiveCoefficientDifferential K Y (n + 1) r).ker := hzpos
    rw [positiveAdditiveCoefficientDifferential_ker] at hm
    exact hm
  let zz : K.nonDegenerate (n + 2) → M := fun s ↦ e (za s)
  have hδ' : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M (n + 2) zz = 0 := by
    funext s
    change _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M (n + 2) (fun t ↦ e (za t)) s = 0
    exact (NormalizedValueCochains.differential_map K (M := N) (N := M)
      e.toAddMonoidHom (n + 2) za s).trans (by
        rw [congrFun hδ s]
        exact map_zero _)
  obtain ⟨a, ha⟩ := NormalizedValueCochains.exists_primitive_of_isZero K M (n + 1) hH zz hδ'
  have hm : zz ∈ (positiveAdditiveCoefficientDifferential K Y n (r + 1)).range := by
    rw [positiveAdditiveCoefficientDifferential_range]
    exact ⟨a, ha⟩
  obtain ⟨c, hc⟩ := hm
  refine ⟨fun s ↦ Additive.toMul (c s), ?_⟩
  funext s
  have he : e (Additive.ofMul
      (coefficientDifferential K Y n (r + 1) (fun s ↦ Additive.toMul (c s)) s)) =
      e (Additive.ofMul (z s)) := congrFun hc s
  exact congrArg Additive.toMul (e.injective he)

end
end SerrePositivity.KST.Spectra.SkeletalCellAttachment
