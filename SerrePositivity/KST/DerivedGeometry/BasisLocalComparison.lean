module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-!
# 開基底上の比較から得る局所単射・局所全射

概要：前層射の基底上の成分を用い、局所的な単射性と全射性を証明する。
方針：任意の点の周りで、指定された開集合に含まれる基底開を選ぶ。
規約：前層自体に層条件を要求しない。
使われ方：KST D4、Toën Derived Azumaya §3.2 のアフィン比較と層化。
-/

@[expose] public section

noncomputable section

universe u v w z

open CategoryTheory TopologicalSpace

namespace SerrePositivity.KST.DerivedGeometry

variable {X : TopCat.{u}} {C : Type v} [Category.{w} C]
  {FC : C → C → Type*} {CC : C → Type u}
  [∀ P Q, FunLike (FC P Q) (CC P) (CC Q)] [ConcreteCategory.{u} C FC]
  {ι : Type z} (B : ι → Opens X) (hB : Opens.IsBasis (Set.range B))
  {P Q : TopCat.Presheaf C X} (φ : P ⟶ Q)

include hB

/--
概要：開基底上で単射な前層射は局所単射。
方針：等しい像を持つ二つの切断を各点の基底近傍へ制限する。
規約：基底成分の単射性だけを使い、層の分離性は不要。
使われ方：KST D4、Toën §3.2 の層化比較の局所単射性。
-/
lemma locallyInjective_of_basis
    (hφ : ∀ i, Function.Injective (φ.app (.op (B i)))) :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) φ := by
  refine ⟨fun {U} x y h p hp => ?_⟩
  obtain ⟨V, ⟨_, ⟨i, rfl⟩, rfl⟩, hpV, hVU⟩ := hB.exists_subset_of_mem_open hp U.unop.isOpen
  refine ⟨B i, homOfLE hVU, ?_, hpV⟩
  apply hφ i
  rw [NatTrans.naturality_apply, NatTrans.naturality_apply, h]

/--
概要：開基底上で全射な前層射は局所全射。
方針：各点で基底近傍へ制限した切断を持ち上げる。
規約：任意の開上の全射性を主張しない。
使われ方：KST D4、Toën §3.2 の層化比較の局所全射性。
-/
lemma locallySurjective_of_basis
    (hφ : ∀ i, Function.Surjective (φ.app (.op (B i)))) :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ := by
  refine ⟨fun {U} s p hp => ?_⟩
  obtain ⟨V, ⟨_, ⟨i, rfl⟩, rfl⟩, hpV, hVU⟩ := hB.exists_subset_of_mem_open hp U.isOpen
  obtain ⟨t, ht⟩ := hφ i (Q.map (homOfLE hVU).op s)
  exact ⟨B i, homOfLE hVU, ⟨t, ht⟩, hpV⟩

end SerrePositivity.KST.DerivedGeometry
