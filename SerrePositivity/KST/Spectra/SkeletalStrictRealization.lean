module

public import SerrePositivity.KST.Spectra.SkeletalFiberRepresentatives

/-!
概要：任意の cochain を低い骨格で厳密に定数な射として実現する。
方針：各係数の代表単体を骨格の pushout で貼り、係数を同じ単体で回収する。
規約：cochain の実際の次数は二以上。
使われ方：Goerss–Jardine VIII §1。塔の微分の比較を任意の係数へ移す。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalSphericalRealization

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 任意の正規化 cochain は、厳密な定数制限を持つ骨格射の cochain。 -/
theorem exists_strict_realization {K : SSet.{u}} (Y : PointedSimplicialSet.{u})
    [KanComplex Y.right] {n : ℕ}
    (a : K.nonDegenerate (n + 2) → Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup Y.right (n + 1) Y.basepoint)) :
    ∃ (f : (K.skeleton (n + 3) : SSet.{u}) ⟶ Y.right)
      (hf : UnbasedPointedMapping.skeletalInclusion K (n + 1) ≫ f = SSet.const Y.basepoint),
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.cochain f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf) = a := by
  choose r hr using fun s ↦ Quotient.exists_rep (Additive.toMul (a s))
  obtain ⟨f, hf, hfr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.exists_map r
  refine ⟨f, hf, ?_⟩
  funext s
  have hs : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf) s.val = r s := by
    apply RelativeMorphism.ext
    exact hfr s
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.additiveClass
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.simplexValue f (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.lower_constant f hf) s.val) = a s
  rw [hs]
  exact congrArg Additive.ofMul (hr s)

end
end SerrePositivity.KST.Spectra.SkeletalSphericalRealization
