module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightFibrationContractible
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：終対象と右 pinched 写像空間の可縮性。
方針：slice 射影の fiber の厳密な同型と全境界の持ち上げを使う。
規約：可縮性には非空性と Kan 性を含む。
使われ方：HTT Proposition 1.2.12.4、Kerodon §4.7.3（Tag 02H6）。

対応節は Kerodon 4.7（Tag 05EA）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 概要：終対象へ向かう右 pinched 写像空間は可縮な Kan 複体。
方針：終対象の slice 射影は trivial Kan fibration なので各 fiber の境界を充填できる。
規約：この向きでは元の単体集合の quasicategory 性を仮定しない。
使われ方：HTT Proposition 1.2.12.4、Kerodon Corollary 4.7.3.12（Tag 06R2） の順方向。 -/
lemma IsTerminalVertex.pinchedHom_isContractibleKan {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) (z : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z x) := by
  have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration x).1 hx
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso z x).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_isContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm x)) z)

/-- 概要：終対象となる頂点はホモトピー圏でも終対象。
方針：右 pinched 写像空間の非空性と連結性を π₀ と Hom の同値で移す。
規約：この比較には元の quasicategory 性を仮定する。
使われ方：HTT §1.2.12、Kerodon §4.7.3（Tag 02H6） の同型不変性。 -/
@[kerodon 02HQ]
noncomputable def IsTerminalVertex.isTerminalHo {X : SSet.{u}} [Quasicategory X]
    {x : X _⦋0⦌} (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) :
    IsTerminal (SSet.HomotopyCategory.mk x : hoFunctor.obj X) := by
  have h (z : hoFunctor.obj X) : Unique (z ⟶ SSet.HomotopyCategory.mk x) := by
    let e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomPiZeroEquiv (X := X) z.as.as x
    have hc := hx.pinchedHom_isContractibleKan z.as.as
    have hs := hc.piZero_subsingleton
    let a := Classical.choice hc.nonempty
    exact ⟨⟨e (SSet.π₀.mk a)⟩, fun f ↦ e.symm.injective (hs.elim _ _)⟩
  exact IsTerminal.ofUnique _

/-- 概要：全ての頂点からの右 pinched 写像空間が可縮なら終対象。
方針：slice 射影の各 fiber の可縮性へ移し、右ファイブレーションの判定を使う。
規約：X の quasicategory 性を仮定する。
使われ方：HTT Proposition 1.2.12.4、Kerodon Corollary 4.7.3.12（Tag 06R2） の逆方向。 -/
lemma isTerminalVertex_of_pinchedHom_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) (h : ∀ z : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z x)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_trivialKanFibration x).2
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_trivialKanFibration_of_contractible_fibers
  intro z
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso z x) (h z)

/-- 概要：終対象性は全ての右 pinched 写像空間の可縮性と同値。
方針：終対象の slice 射影の trivial Kan fibration 性と fiber の判定を合わせる。
規約：可縮性は零次元を含む全境界の充填で、非空性と Kan 性を含む。
使われ方：HTT Proposition 1.2.12.4、Kerodon Corollary 4.7.3.12（Tag 06R2）。 -/
@[kerodon 02H7]
lemma isTerminalVertex_iff_pinchedHom_isContractibleKan {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x ↔
      ∀ z : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom z x) :=
  ⟨fun h z ↦ h.pinchedHom_isContractibleKan z,
    isTerminalVertex_of_pinchedHom_isContractibleKan x⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "1.2.12.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_iff_pinchedHom_isContractibleKan
