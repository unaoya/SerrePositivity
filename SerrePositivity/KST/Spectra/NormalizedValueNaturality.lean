module

public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.Subdivision.NormalizedValueCochains

/-!
概要：元を値とする正規化微分の係数に関する自然性。
方針：零延長・交代和・整数倍が加法準同型と交換することを使う。
規約：係数は任意の可換加法群。
使われ方：Goerss–Jardine III §2、VIII §1。loop の係数同型による微分の移送。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.NormalizedValueCochains

noncomputable section

/-- 係数の加法準同型は退化単体での零延長と可換。 -/
lemma zeroExtend_map (K : SSet.{u}) {M N : AddCommGrpCat.{u}} (f : M →+ N)
    (n : ℕ) (a : K.nonDegenerate n → M) (s : K _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.zeroExtend K N n (fun t ↦ f (a t)) s = f (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.zeroExtend K M n a s) := by
  classical
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.zeroExtend]
  split_ifs <;> simp only [map_zero]

/-- 通常の正規化交代微分は任意の係数準同型と可換。 -/
lemma differential_map (K : SSet.{u}) {M N : AddCommGrpCat.{u}} (f : M →+ N)
    (n : ℕ) (a : K.nonDegenerate n → M) (s : K.nonDegenerate (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K N n (fun t ↦ f (a t)) s = f (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K M n a s) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential_apply, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential_apply, map_sum]
  simp only [zeroExtend_map, map_zsmul]

end
end SerrePositivity.KST.Spectra.NormalizedValueCochains
