module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober

/-!
概要：Noether スキームの稠密開の点から任意の点への特殊化を選ぶ。
方針：点を含む既約成分の一般点を取り、成分に含まれる非空開集合で稠密性を使う。
規約：稠密開を個々の点の閉包上で稠密と仮定しない。
使われ方：v 判定から狭義変換の全射性を得る G1 の接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry TopologicalSpace
universe u

/-- Noether スキームの任意の点は、稠密開のある点の特殊化。 -/
theorem exists_specialization_from_denseOpen (Y : Scheme.{u})
    [_root_.AlgebraicGeometry.IsNoetherian Y] (U : Y.Opens) (hU : Dense U.carrier) (y : Y) :
    ∃ p : Y, p ∈ U ∧ p ⤳ y := by
  let C := irreducibleComponent y
  have hC := irreducibleComponent_mem_irreducibleComponents y
  let p := hC.1.genericPoint
  have hp : IsGenericPoint p C := hC.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
  obtain ⟨O, hO, hOne, hOC⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  obtain ⟨x, hxO, hxU⟩ := hU.inter_open_nonempty O hO hOne
  refine ⟨p, (hp.mem_open_set_iff U.isOpen).mpr ⟨x, hOC hxO, hxU⟩, ?_⟩
  exact hp.specializes mem_irreducibleComponent

end SerrePositivity.AlgebraicGeometry
