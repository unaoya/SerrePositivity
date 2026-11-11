module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SequentialNerveSupports
public import Mathlib.AlgebraicTopology.SimplicialSet.Subcomplex
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular

/-!
概要：可算 nerve の隣接辺と全頂点からなる spine を部分複体として定義する。
方針：全頂点番号の差が高々一という条件を、単体の再添字に対して保持する。
規約：全ての退化単体を含め、可算 nerve 自体は変更しない。
使われ方：P-11 の望遠鏡形状と可算 nerve の共終比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：有限頂点集合が一つの隣接辺に収まる条件。
方針：全ての二頂点の番号差を一以下に抑える。
規約：空集合と一頂点集合も許す。
使われ方：spine 所属の有限集合による判定。 -/
def SequentialSpineSupport (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, b ≤ a + 1

/-- 概要：可算 nerve の隣接辺と全頂点からなる部分複体。
方針：頂点番号の差の条件は任意の単体的再添字に保たれる。
規約：高次の退化単体を落とさない。
使われ方：望遠鏡の像と inner horn 接合の出発領域。 -/
def sequentialSpine : (nerve (ULift.{u} ℕ)).Subcomplex where
  obj _ := {s | ∀ i j, (s.obj j).down ≤ (s.obj i).down + 1}
  map {_ _} α _ hs i j := hs
    ((SimplexCategory.toCat.map α.unop).toFunctor.obj i)
    ((SimplexCategory.toCat.map α.unop).toFunctor.obj j)

/-- 概要：非退化単体の spine 所属は有限頂点集合の条件と一致する。
方針：各頂点の番号と有限像の所属を双方向に展開する。
規約：単体の全頂点についての条件を使う。
使われ方：領域外の単体を有限集合の pairing へ移す。 -/
lemma sequentialNerve_mem_spine_iff_support (s : (nerve (ULift.{u} ℕ)).N) :
    s.simplex ∈ sequentialSpine.obj (Opposite.op ⦋s.dim⦌) ↔
      SequentialSpineSupport (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s) := by
  constructor
  · intro h a ha b hb
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
    exact h i j
  · intro h i j
    exact h _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)

/-- 概要：有限頂点集合の包含は、元の非退化単体の面関係と一致する。
方針：poset の nerve における生成部分複体の判定へ、持ち上げの全単射を使う。
規約：任意の余次元の面を許す。
使われ方：pairing の proper 性と祖先関係の順位。 -/
lemma sequentialNerveSupport_subset_iff (s t : (nerve (ULift.{u} ℕ)).N) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport s ⊆ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sequentialNerveSupport t ↔ s ≤ t := by
  change _ ↔ Subcomplex.ofSimplex s.simplex ≤ Subcomplex.ofSimplex t.simplex
  rw [PartialOrder.nerve_ofSimplex_le_ofSimplex_iff]
  constructor
  · intro h x hx
    obtain ⟨i, rfl⟩ := hx
    have hm := h (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    exact ⟨j, ULift.ext hj⟩
  · intro h a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj⟩ := h ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg ULift.down hj⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
