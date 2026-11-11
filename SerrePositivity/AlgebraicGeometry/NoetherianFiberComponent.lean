module

public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Connected.Clopen

/-!
概要：Noether 空間の連結成分は開かつ閉である。
方針：成分の補集合を、それと交わらない有限個の既約成分で覆う。
規約：空間の分離公理を仮定しない。
使われ方：指定ファイバーの連結成分を開部分として取り出す。
-/

@[expose] public section

namespace SerrePositivity.AlgebraicGeometry

open TopologicalSpace

/--
概要：Noether 空間の一点を含む連結成分は開かつ閉。
方針：補集合を、その点の連結成分と交わらない既約成分の有限和として表す。
規約：連結成分は位相空間の `connectedComponent` を使う。
使われ方：相対正規化先の Noether なファイバーで成分を選ぶ。
-/
theorem isClopen_connectedComponent_of_noetherianSpace
    {X : Type*} [TopologicalSpace X] [NoetherianSpace X] (x : X) :
    IsClopen (connectedComponent x) := by
  let C := connectedComponent x
  let S := {Z ∈ irreducibleComponents X | Disjoint Z C}
  have hS : S.Finite :=
    NoetherianSpace.finite_irreducibleComponents.subset (fun _ hz => hz.1)
  have hSC : ⋃₀ S = Cᶜ := by
    ext y
    constructor
    · rintro ⟨Z, hZ, hy⟩
      exact fun h => Set.disjoint_left.mp hZ.2 hy h
    · intro hy
      have hy' : y ∈ ⋃₀ irreducibleComponents X := by
        rw [sUnion_irreducibleComponents]
        exact Set.mem_univ _
      obtain ⟨Z, hZ, hyZ⟩ := hy'
      refine ⟨Z, ⟨hZ, Set.disjoint_left.mpr ?_⟩, hyZ⟩
      intro z hzZ hzC
      have hyC : y ∈ connectedComponent z := hZ.1.isConnected.subset_connectedComponent hzZ hyZ
      change y ∉ connectedComponent x at hy
      apply hy
      rwa [connectedComponent_eq hzC]
  have hc : IsClosed Cᶜ := by
    rw [← hSC, Set.sUnion_eq_biUnion]
    exact hS.isClosed_biUnion fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
  exact ⟨isClosed_connectedComponent, isClosed_compl_iff.mp hc⟩

end SerrePositivity.AlgebraicGeometry
