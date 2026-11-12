module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderCoproduct
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinCylinderGluing
public import Mathlib.AlgebraicTopology.SimplicialSet.Skeleton

/-!
概要：相対骨格の一段に沿う写像円柱比較の同値条件の拡張。
方針：境界と標準単体の族の比較を coproduct で貼り、骨格の pushout に適用する。
規約：共通の終域への構造射は任意。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、始域の次元による帰納。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet SSet.relativeCellComplexOfMono
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：現在の骨格と追加する各セルおよび境界の比較から次の骨格の比較が従う。
方針：構造射を保つ二つの coproduct の比較と Over 圏へ持ち上げた骨格の pushout を使う。
規約：相対骨格の基準の射 i は単射。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セルを同時に貼る帰納段階。 -/
lemma isPrecompositionEquivalence_relativeJoinCylinderComparison_skeleton_succ
    {A X S : SSet.{u}} (i : A ⟶ X) [Mono i] (f : X ⟶ S) (d : ℕ)
    (hprev : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison ((skeletonOfMono i d).ι ≫ f)))
    (hboundary : ∀ c : Cell i d, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison ((boundary d).ι ≫ c.map ≫ f)))
    (hcell : ∀ c : Cell i d, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison (c.map ≫ f))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison ((skeletonOfMono i (d + 1)).ι ≫ f)) := by
  let a : Over S := Over.mk (l i d ≫ b i d ≫ (skeletonOfMono i (d + 1)).ι ≫ f)
  let b₀ : Over S := Over.mk (b i d ≫ (skeletonOfMono i (d + 1)).ι ≫ f)
  let c₀ : Over S := Over.mk ((skeletonOfMono i d).ι ≫ f)
  let d₀ : Over S := Over.mk ((skeletonOfMono i (d + 1)).ι ≫ f)
  have hw : t i d ≫ (skeletonOfMono i d).ι ≫ f =
      l i d ≫ b i d ≫ (skeletonOfMono i (d + 1)).ι ≫ f := by
    have h := congrArg (fun k : sigmaBoundary i d ⟶ (skeletonOfMono i (d + 1) : SSet.{u}) ↦
      k ≫ (skeletonOfMono i (d + 1)).ι ≫ f) (w i d)
    simp only [Category.assoc] at h
    rw [← Category.assoc (r i d) (skeletonOfMono i (d + 1)).ι f] at h
    simpa only [r, Subcomplex.homOfLE_ι] using h
  let u₀ : a ⟶ b₀ := Over.homMk (l i d) rfl
  let v₀ : a ⟶ c₀ := Over.homMk (t i d) hw
  let r₀ : b₀ ⟶ d₀ := Over.homMk (b i d) rfl
  let s₀ : c₀ ⟶ d₀ := Over.homMk (r i d) (by
    change r i d ≫ ((skeletonOfMono i (d + 1)).ι ≫ f) = (skeletonOfMono i d).ι ≫ f
    rw [← Category.assoc]
    rfl)
  have hp : IsPushout u₀ v₀ r₀ s₀ := by
    apply IsPushout.of_map_of_faithful (Over.forget S)
    exact (SSet.relativeCellComplexOfMono.isPushout i d).flip
  have hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison a.hom) := by
    have he : a.hom = Sigma.desc
        (fun c : Cell i d ↦ (boundary d).ι ≫ c.map ≫ f) := by
      apply Sigma.hom_ext
      intro c
      rw [Sigma.ι_comp_desc]
      change c.ιSigmaBoundary ≫ (l i d ≫ b i d ≫ (skeletonOfMono i (d + 1)).ι ≫ f) = _
      simp only [← Category.assoc]
      rw [Cell.ι_l]
      simp only [Category.assoc]
      rw [reassoc_of% Cell.ι_b_ι c]
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_sigma
      (fun _ : Cell i d ↦ (boundary d : SSet.{u})) _ hboundary
  have hB : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison b₀.hom) := by
    have he : b₀.hom = Sigma.desc (fun c : Cell i d ↦ c.map ≫ f) := by
      apply Sigma.hom_ext
      intro c
      rw [Sigma.ι_comp_desc]
      change c.ιSigmaStdSimplex ≫ (b i d ≫ (skeletonOfMono i (d + 1)).ι ≫ f) = c.map ≫ f
      exact (reassoc_of% Cell.ι_b_ι c) f
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_sigma
      (fun _ : Cell i d ↦ (Δ[d] : SSet.{u})) _ hcell
  have : Mono u₀.left := inferInstanceAs (Mono (l i d))
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison d₀.hom)
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.isPrecompositionEquivalence_relativeJoinCylinderComparison_of_pushout hp hA hB
  exact hprev

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
