module

public import SerrePositivity.KST.Spectra.SkeletalMapSimplex
public import SerrePositivity.KST.Spectra.LoopFundamentalCommutativity

/-!
概要：loop 値の骨格射の次数一の正規化 cochain とその厳密な実現。
方針：境界定数の辺の類を取り、退化辺の零性と骨格 pushout を使う。
規約：loop 基本群の既存の積の可換性による加法表示。
使われ方：Goerss–Jardine III §2、VIII §1。次数一の係数微分の比較。
-/

@[expose] public section
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.SkeletalEdgeCochain

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open SkeletalCellAttachment UnbasedPointedMapping

variable (K : SSet.{u}) (Y : PointedSimplicialSet.{u}) [KanComplex Y.right]
  (f : (K.skeleton 2 : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right)
  (hf : skeletalInclusion K 0 ≫ f = SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)

/-- 頂点で定数の loop 値の射の、非退化辺ごとの加法的係数。 -/
def cochain : K.nonDegenerate 1 →
    Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right 0 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint) :=
  fun s ↦ Additive.ofMul (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
    (SkeletalMapSimplex.simplex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0 f hf s.val))

/-- 退化辺での零延長は、全ての辺で同じ境界定数単体の類になる。 -/
lemma zeroExtend (s : K _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.zeroExtend K
      (AddCommGrpCat.of (Additive
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right 0 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint))) 1
      (cochain K Y f hf) s = Additive.ofMul
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SkeletalMapSimplex.simplex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0 f hf s)) := by
  classical
  unfold _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.zeroExtend
  split_ifs with hs
  · rfl
  · have hd : s ∈ K.degenerate 1 := (K.mem_degenerate_iff_notMem_nonDegenerate s).2 hs
    rw [K.degenerate_eq_iUnion_range_σ] at hd
    obtain ⟨i, t, rfl⟩ := Set.mem_iUnion.mp hd
    rw [SkeletalMapSimplex.simplex_degeneracy]
    rfl

/-- 次数一の cochain の微分は、各二単体の三辺の通常の交代和。 -/
lemma differential (s : K.nonDegenerate 2) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential K
      (AddCommGrpCat.of (Additive
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right 0 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint))) 1
      (cochain K Y f hf) s =
    ∑ j : Fin 3, (-1 : ℤ) ^ j.val • Additive.ofMul
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (SkeletalMapSimplex.simplex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0 f hf (K.δ j s.val))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NormalizedValueCochains.differential_apply]
  simp only [zeroExtend]

/-- 次数一の cochain は元の骨格射の実際の fiber 成分係数。 -/
lemma fiberVertex_cochain :
    (fun s ↦ Additive.ofMul (stageFiberComponentEquiv K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0
      (π₀.mk (skeletalFiberVertex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0 f hf)) s)) = cochain K Y f hf := by
  funext s
  exact congrArg Additive.ofMul
    (SkeletalMapSimplex.fiberVertex_coefficient K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0 f hf s)

/-- 任意の次数一の loop 係数は、頂点で厳密に定数な骨格射として実現できる。 -/
theorem exists_realization (c : K.nonDegenerate 1 →
    Additive (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right 0 (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint)) :
    ∃ (f : (K.skeleton 2 : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).right)
      (hf : skeletalInclusion K 0 ≫ f = SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).basepoint),
      cochain K Y f hf = c := by
  choose r hr using fun s ↦ Quotient.exists_rep (Additive.toMul (c s))
  obtain ⟨f, hf, hfr⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.exists_map r
  refine ⟨f, hf, ?_⟩
  funext s
  have hs : SkeletalMapSimplex.simplex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0 f hf s.val = r s := by
    apply RelativeMorphism.ext
    exact hfr s
  change Additive.ofMul (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk
    (SkeletalMapSimplex.simplex K (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y) 0 f hf s.val)) = c s
  rw [hs]
  exact congrArg Additive.ofMul (hr s)

end
end SerrePositivity.KST.Spectra.SkeletalEdgeCochain
