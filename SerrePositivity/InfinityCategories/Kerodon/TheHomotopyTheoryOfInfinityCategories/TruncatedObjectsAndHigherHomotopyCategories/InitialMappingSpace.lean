module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialOpposite

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.ContractibleKan
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalMappingSpace

/-!
概要：始対象性を左 pinched 写像空間の可縮性で判定する。
方針：境界の反転で可縮性を移し、既存の終対象判定を双対化する。
規約：Core・Stable は読み取り専用で利用し、straightening に依存しない。
使われ方：Kerodon §4.7.3（Tag 02H6） と §6.2.6 の comma 内の普遍矢印の判定。

対応節は Kerodon 4.7（Tag 05EA）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-- 概要：反転した単体集合が可縮なら元の単体集合も可縮。
方針：反転した境界を充填し、二重反転で元の充填を回収する。
規約：quasicategory 性も Kan 性も事前には仮定しない。
使われ方：左写像空間の反転を消去する。 -/
lemma isContractibleKan_of_op {K : SSet.{u}} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K.op) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K := by
  intro n b
  obtain ⟨F, hF⟩ := h n (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap n b)
  exact _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.boundaryFiller_of_reverseBoundaryFiller n b F hF

/-- 概要：可縮な単体集合の反転も可縮。
方針：二重反転した境界を元の単体集合で充填して戻す。
規約：境界の全次元を含み、非空性も保つ。
使われ方：終対象判定を左写像空間へ移す。 -/
lemma IsContractibleKan.op {K : SSet.{u}} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K.op := by
  intro n b
  let q := (SSet.opFunctorCompOpFunctorIso.app K).hom
  obtain ⟨F, hF⟩ := h n (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap n b ≫ q)
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.boundaryFiller_of_reverseBoundaryFiller n b
    (F ≫ (SSet.opFunctorCompOpFunctorIso.app K).inv)
  rw [← Category.assoc, hF]
  change (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.reverseBoundaryMap n b ≫ (SSet.opFunctorCompOpFunctorIso.app K).hom) ≫
    (SSet.opFunctorCompOpFunctorIso.app K).inv = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan export _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsContractibleKan (op)


/-- 概要：可縮性は単体集合の反転で検出できる。
方針：境界充填の反転による両方向を合わせる。
規約：任意の単体集合。
使われ方：左右の pinched 模型に対する可縮性の比較。 -/
lemma isContractibleKan_op_iff (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K.op ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan K :=
  ⟨isContractibleKan_of_op, IsContractibleKan.op⟩

/-- 概要：始対象から出る左 pinched 写像空間は可縮。
方針：始対象を終対象へ反転し、右模型の可縮性を再び反転する。
規約：この向きには元の単体集合の quasicategory 性は不要。
使われ方：comma の始対象から普遍矢印の写像空間条件を得る。 -/
lemma IsInitialVertex.pinchedHomLeft_isContractibleKan {X : SSet.{u}} {x : X _⦋0⦌}
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x) (y : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) :=
  (hx.op_isTerminalVertex.pinchedHom_isContractibleKan (SSet.opObjEquiv.symm y)).op

/-- 概要：全ての左 pinched 写像空間が可縮な頂点は始対象。
方針：反転した単体集合の終対象判定へ戻す。
規約：X の quasicategory 性を仮定する。
使われ方：局所存在判定で comma の写像空間の可縮性から始対象を得る。 -/
lemma isInitialVertex_of_pinchedHomLeft_isContractibleKan {X : SSet.{u}}
    [Quasicategory X] (x : X _⦋0⦌)
    (h : ∀ y : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isInitialVertex_of_isTerminalVertex_op
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.isTerminalVertex_of_pinchedHom_isContractibleKan
  intro y
  exact isContractibleKan_of_op (h (SSet.opObjEquiv y))

/-- 概要：始対象性は全ての左 pinched 写像空間の可縮性と同値。
方針：終対象の右模型での判定の双対の両方向を合わせる。
規約：可縮性は零次元を含む全境界の充填を意味する。
使われ方：Kerodon §4.7.3（Tag 02H6）、§6.2.6（Tag 02FQ） の普遍矢印性の検出。 -/
lemma isInitialVertex_iff_pinchedHomLeft_isContractibleKan {X : SSet.{u}}
    [Quasicategory X] (x : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x ↔
      ∀ y : X _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft x y) :=
  ⟨fun h y ↦ h.pinchedHomLeft_isContractibleKan y,
    isInitialVertex_of_pinchedHomLeft_isContractibleKan x⟩

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.1.3.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsContractibleKan.op
