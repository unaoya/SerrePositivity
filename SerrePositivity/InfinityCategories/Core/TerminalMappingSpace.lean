module

public import SerrePositivity.InfinityCategories.Core.PinchedSlice

/-!
概要：終対象と右 pinched 写像空間の可縮性。
方針：slice 射影の fiber の厳密な同型と全境界の持ち上げを使う。
規約：可縮性には非空性と Kan 性を含む。
使われ方：HTT Proposition 1.2.12.4、Kerodon §4.7.3。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：終対象へ向かう右 pinched 写像空間は可縮な Kan 複体。
方針：終対象の slice 射影は trivial Kan fibration なので各 fiber の境界を充填できる。
規約：この向きでは元の単体集合の quasicategory 性を仮定しない。
使われ方：HTT Proposition 1.2.12.4、Kerodon Proposition 4.7.3.12 の順方向。 -/
lemma IsTerminalVertex.pinchedHom_isContractibleKan {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : IsTerminalVertex x) (z : X _⦋0⦌) : IsContractibleKan (pinchedHom z x) := by
  have := (isTerminalVertex_iff_trivialKanFibration x).1 hx
  exact isContractibleKan_of_iso (pinchedHomSliceFiberIso z x).symm
    (vertexFiber_isContractibleKan (sliceOverProjection (SSet.yonedaEquiv.symm x)) z)

/-- 概要：終対象となる頂点はホモトピー圏でも終対象。
方針：右 pinched 写像空間の非空性と連結性を π₀ と Hom の同値で移す。
規約：この比較には元の quasicategory 性を仮定する。
使われ方：HTT §1.2.12、Kerodon §4.7.3 の同型不変性。 -/
noncomputable def IsTerminalVertex.isTerminalHo {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (hx : IsTerminalVertex x) :
    IsTerminal (SSet.HomotopyCategory.mk x : hoFunctor.obj X) := by
  have h (z : hoFunctor.obj X) : Unique (z ⟶ SSet.HomotopyCategory.mk x) := by
    let e := pinchedHomPiZeroEquiv (X := X) z.as.as x
    have hc := hx.pinchedHom_isContractibleKan z.as.as
    have hs := hc.piZero_subsingleton
    let a := Classical.choice hc.nonempty
    exact ⟨⟨e (SSet.π₀.mk a)⟩, fun f ↦ e.symm.injective (hs.elim _ _)⟩
  exact IsTerminal.ofUnique _

end SerrePositivity.InfinityCategories
