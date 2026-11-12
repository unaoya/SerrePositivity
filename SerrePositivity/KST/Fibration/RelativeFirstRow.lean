module
public import SerrePositivity.KST.Fibration.RelativeSQuotient
public import SerrePositivity.KST.SConstruction.FirstRowFibration
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.SubcomplexInverseImageComparison

/-!
概要：元の相対 gapped S• の商比較を、同じ有限第一行の相対図式へ接続する。
方針：K-S• 正本の第一行制限と全評価の core 判定を同じ相対部分複体へ制限する。
規約：一般の局所化・商 API は新設せず、有限線型図式の局所化は Sp の供給を待つ。
使われ方：K-6 c5 の正段商比較の gapped 側と有限第一行側の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ)

private theorem firstRowCore_preimage (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C.obj) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (firstRowNerve n)).obj C.obj)).preimage
        (firstRowRestriction n C.obj) := by
  ext d s
  change (∀ α : ⦋1⦌ ⟶ d.unop,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((sConstruction n C.obj).map α.op s))) ↔
      ∀ α : ⦋1⦌ ⟶ d.unop, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
        (((ihom (firstRowNerve n)).obj C.obj).map α.op
          ((firstRowRestriction n C.obj).app d s)))
  constructor
  · intro hs α
    rw [← NatTrans.naturality_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr rfl).mp
      ((hs α).map (firstRowRestriction n C.obj))
  · intro hs α
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isFullyFaithful_of_trivialKanFibration (firstRowRestriction n C.obj)).reflects_isInvertibleEdge
    have hi := hs α
    rw [← NatTrans.naturality_apply] at hi
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr rfl).mpr hi

/-- 概要：同じ第一行制限は元の完全商関手による後合成を厳密に保つ。
方針：gapped 包含後の後合成と内部 Hom の自然性を使う。
規約：選択した第一行の逆射を使わず、元の全単体写像を保持する。
使われ方：相対 gapped 部分複体と第一行の相対条件を照合する。 -/
theorem relativeFirstRow_postcomp :
    sPostcomp n q.hom (exactMap_preservesSData q) ≫ firstRowRestriction n C.obj =
      firstRowRestriction n B.obj ≫ (ihom (firstRowNerve n)).map q.hom := by
  unfold firstRowRestriction
  rw [← Category.assoc, sPostcomp_ι, Category.assoc, (pre (firstRowInclusion n)).naturality]
  simp only [Category.assoc]

/-- 概要：同じ有限第一行で商像が全て可逆となる全相対図式。
方針：同じ第一行の商関手の下で core の厳密な逆像を取る。
規約：局所化性やこの比較の弱同値性は定義に含めない。
使われ方：Sp の有限線型図式供給を元の相対 S• と接続する場所。 -/
def relativeFirstRow : ((ihom (firstRowNerve n)).obj B.obj).Subcomplex :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (firstRowNerve n)).obj C.obj)).preimage
    ((ihom (firstRowNerve n)).map q.hom)

/-- 概要：元の相対 S_n の全高次条件は、同じ相対第一行の厳密な逆像。
方針：全 gapped 商比較の core 逆像と、第一行制限の同値による可逆性反映を使う。
規約：全 Ar 成分を第一行の頂点だけの照合で代用せず、core 全体の条件を使う。
使われ方：元の相対 S_n から有限第一行への底変換。 -/
theorem relativeSConstruction_eq_firstRow_preimage :
    relativeSConstruction q.hom n = (relativeFirstRow q n).preimage
      (firstRowRestriction n B.obj) := by
  have h := relativeDiagram_eq_fullFunctorCore_preimage q.hom (gappedSubcomplex n B.obj).ι _
    (sPostcomp n q.hom (exactMap_preservesSData q)) rfl
  change relativeSConstruction q.hom n =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C.obj)).preimage
      (sPostcomp n q.hom (exactMap_preservesSData q)) at h
  rw [h, firstRowCore_preimage, ← Subcomplex.preimage_comp,
    relativeFirstRow_postcomp, Subcomplex.preimage_comp]
  rfl

/-- 概要：元の相対 S_n から同じ相対第一行への実制限写像。
方針：厳密な逆像表示を通って元の第一行制限を底変換する。
規約：元の全 gapped 図式と商射を保持する。
使われ方：正段の商実現比較を有限第一行へ移す。 -/
def relativeFirstRowRestriction : (relativeSConstruction q.hom n : SSet.{u}) ⟶
    (relativeFirstRow q n : SSet.{u}) :=
  (Subcomplex.eqToIso (relativeSConstruction_eq_firstRow_preimage q n)).hom ≫
    (relativeFirstRow q n).fromPreimage (firstRowRestriction n B.obj)

/-- 概要：同じ相対第一行制限の包含後は、元の相対 S_n 包含と第一行制限の合成。
方針：同じ逆像の射影の指定式を使う。
規約：全単体写像の厳密等式。
使われ方：元の商比較への全図式の接続。 -/
theorem relativeFirstRowRestriction_ι :
    relativeFirstRowRestriction q n ≫ (relativeFirstRow q n).ι =
      (relativeSConstruction q.hom n).ι ≫ firstRowRestriction n B.obj := by
  rw [relativeFirstRowRestriction, Category.assoc, Subcomplex.fromPreimage_ι, ← Category.assoc]
  rfl

/-- 概要：同じ相対第一行制限は trivial Kan fibration。
方針：K-S• 正本の第一行制限の全境界持ち上げ性を同じ相対部分複体へ底変換する。
規約：有限線型図式の商局所化は仮定しない。
使われ方：相対 gapped 図式と有限第一行の全高次の比較。 -/
instance relativeFirstRowRestriction_trivialKanFibration :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (relativeFirstRowRestriction q n) := by
  let A := relativeFirstRow q n
  let p := firstRowRestriction n B.obj
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (A.fromPreimage p) :=
    ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.of_isPullback (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.subcomplexInverseImage_isPullback p A).flip
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem⟩
  unfold relativeFirstRowRestriction
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem⟩

end SerrePositivity.KST.Fibration
