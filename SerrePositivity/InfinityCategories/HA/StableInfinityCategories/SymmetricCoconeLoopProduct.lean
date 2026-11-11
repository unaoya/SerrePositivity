module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricCoconeTransportKernelPair
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.KanKernelPairLoopProduct
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.SymmetricCoconeLoopSwap

/-! # 対称 span の余錐空間の連結成分上のループ積

概要：全体の余錐空間の π₀ にループ積と単位を移し、二枝交換が右逆元になることを示す。
方針：自己引き戻しの標準同型を通して既存の積・対角・交換の公式を移す。
規約：枝の基点を固定する。使われ方：余極限の Hom 表示へ移す具体的な演算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：単体集合の同型が誘導する連結成分の写像は単射。
方針：同型からの型同値の単射性を抽象的な同型に対して使う。
規約：充填性不要。使われ方：大きな幾何学的同型を展開せず連結成分の等号を判定する。 -/
lemma stableMapPiZeroIso_injective {A B : SSet.{u}} (i : A ≅ B) :
    Function.Injective (SSet.mapπ₀ i.hom) := (SSet.π₀Functor.mapIso i).toEquiv.injective

/-- 概要：対称 span の余錐空間の連結成分に枝の自己引き戻しのループ積を移す。
方針：標準同型で自己引き戻しへ送り、積を同型の逆で戻す。
規約：枝の終点は始対象、枝の余錐の基点を固定。使われ方：Hom の射の演算との比較。 -/
def symmetricCoconeLoopProduct {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (a b : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y) :=
  SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).inv
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairLoopProduct (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y)
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeMappingSpace_edge_isContractibleKan _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEdgeSimplex_target_initial f hz) y) e
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom a)
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom b))

/-- 概要：対称 span の余錐空間のループ積は自己引き戻し表示で元の積になる。
方針：同型の逆と順方向の連結成分の作用を打ち消す。
規約：基点は固定。使われ方：積の単位・逆元・自然性の転送。 -/
lemma symmetricCoconeLoopProduct_kernelPair {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (a b : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom (symmetricCoconeLoopProduct f hz y e a b) =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairLoopProduct (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y)
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeMappingSpace_edge_isContractibleKan _ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.stableEdgeSimplex_target_initial f hz) y) e
        (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom a)
        (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom b) := by
  rw [symmetricCoconeLoopProduct, ← SSet.mapπ₀_comp_apply, Iso.inv_hom_id, SSet.mapπ₀_id_apply]

/-- 概要：枝の余錐の対角の成分を全体の余錐空間のループ単位とする。
方針：対角の基点を自己引き戻しの標準同型の逆で戻す。
規約：枝の終点の始対象性や値域の充填性は不要。使われ方：Hom 表示の零射との照合。 -/
def symmetricCoconeLoopUnit {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y) :=
  SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).inv
    (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairDiagonal (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y))
      (SSet.π₀.mk e))

/-- 概要：全体のループ単位は自己引き戻し表示で枝の対角の成分になる。
方針：標準同型の順逆を打ち消す。
規約：充填性の仮定なし。使われ方：単位の公式を全体へ移す。 -/
lemma symmetricCoconeLoopUnit_kernelPair {X : SSet.{u}} {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (y : X _⦋0⦌)
    (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌) :
    SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y).hom (symmetricCoconeLoopUnit f y e) =
      SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairDiagonal (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.coconeBranchSource (SSet.yonedaEquiv.symm f.edge) y))
        (SSet.π₀.mk e) := by
  rw [symmetricCoconeLoopUnit, ← SSet.mapπ₀_comp_apply, Iso.inv_hom_id, SSet.mapπ₀_id_apply]

/-- 概要：枝の対角から得る単位は全体のループ積の左単位。
方針：自己引き戻しの同型の単射性と元のループ積の左単位を使う。
規約：指定した枝の基点。使われ方：Hom へ移した演算の単位の検証。 -/
lemma symmetricCoconeLoopProduct_unit_left {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    symmetricCoconeLoopProduct f hz y e (symmetricCoconeLoopUnit f y e) a = a := by
  apply stableMapPiZeroIso_injective (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y)
  rw [symmetricCoconeLoopProduct_kernelPair, symmetricCoconeLoopUnit_kernelPair,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairLoopProduct_diagonal_left]

/-- 概要：枝の対角から得る単位は全体のループ積の右単位。
方針：自己引き戻しの同型の単射性と元のループ積の右単位を使う。
規約：左単位と同じ基点。使われ方：加法の一般判定に必要な両側単位。 -/
lemma symmetricCoconeLoopProduct_unit_right {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    symmetricCoconeLoopProduct f hz y e a (symmetricCoconeLoopUnit f y e) = a := by
  apply stableMapPiZeroIso_injective (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y)
  rw [symmetricCoconeLoopProduct_kernelPair, symmetricCoconeLoopUnit_kernelPair,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairLoopProduct_diagonal_right]

/-- 概要：対称 span の二枝交換は全体のループ積の右逆元。
方針：交換の自己引き戻し表示と元のループ積の右逆元の式を使う。
規約：加法への同定はまだ行わない。使われ方：負号へ移すための逆元の公式。 -/
lemma symmetricCoconeLoopProduct_swap {X : SSet.{u}} [Quasicategory X] {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex z)
    (y : X _⦋0⦌) (e : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (SSet.yonedaEquiv.symm f.edge) y) _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.edgeSpan f f) y)) :
    symmetricCoconeLoopProduct f hz y e a (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeSwap f y) a) =
      symmetricCoconeLoopUnit f y e := by
  apply stableMapPiZeroIso_injective (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso f y)
  rw [symmetricCoconeLoopProduct_kernelPair, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.symmetricCoconeKernelPairIso_swap_piZero,
    symmetricCoconeLoopUnit_kernelPair, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.kanKernelPairLoopProduct_swap]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
