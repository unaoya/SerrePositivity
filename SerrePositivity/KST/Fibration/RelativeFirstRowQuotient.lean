module
public import SerrePositivity.KST.Fibration.RelativeFirstRow
public import SerrePositivity.KST.SConstruction.LocalizedTrivialFibrations
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.CoreEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.KanAnodyneLocalization

/-!
概要：元の相対 gapped S_n の商比較を、同じ有限第一行の商比較へ厳密に移す。
方針：相対第一行制限と core の第一行同値が作る同じ可換四角形を使う。
規約：第一行の商比較の可逆性自体は Sp 正本の供給を待ち、一般局所化 API は新設しない。
使われ方：K-6 c5 の正段商実現比較の具体的な有限図式への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration
variable {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) (n : ℕ)

/-- 概要：同じ相対第一行から元の商第一行の core への実比較。
方針：同じ商関手による後合成の core 逆像の指定射影を使う。
規約：全有限第一行と同じ商射を保持する。
使われ方：Sp の有限図式供給を受ける具体的な比較射。 -/
def relativeFirstRowQuotient : (relativeFirstRow q n : SSet.{u}) ⟶
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (firstRowNerve n)).obj C.obj) : SSet.{u}) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (firstRowNerve n)).obj C.obj)).fromPreimage
    ((ihom (firstRowNerve n)).map q.hom)

/-- 概要：同じ第一行商比較の core 包含後は、元の商関手の後合成そのもの。
方針：同じ逆像部分複体の指定射影を回収する。
規約：全単体写像の厳密等式。
使われ方：元の gapped 商比較の四角形との照合。 -/
theorem relativeFirstRowQuotient_ι :
    relativeFirstRowQuotient q n ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (firstRowNerve n)).obj C.obj)).ι =
      (relativeFirstRow q n).ι ≫ (ihom (firstRowNerve n)).map q.hom := rfl

/-- 概要：元の相対 S_n の商比較と同じ第一行の商比較は、実制限を保つ可換四角形。
方針：同じ core 包含で消去し、元の後合成と第一行の厳密自然性を使う。
規約：四つの元の全単体写像を保持する。
使われ方：正段の商実現比較を有限第一行へ移す。 -/
theorem relativeFirstRowQuotient_square :
    relativeFirstRowRestriction q n ≫ relativeFirstRowQuotient q n =
      relativeSQuotientMap q n ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (firstRowRestriction n C.obj) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom (firstRowNerve n)).obj C.obj)).ι).mp
  rw [Category.assoc, relativeFirstRowQuotient_ι, ← Category.assoc,
    relativeFirstRowRestriction_ι, Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι]
  rw [← relativeFirstRow_postcomp q n]
  rw [← Category.assoc (relativeSQuotientMap q n)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (sConstruction n C.obj)).ι (firstRowRestriction n C.obj),
    relativeSQuotientMap_ι]
  simp only [Category.assoc]

/-- 概要：元の相対 gapped 商比較の局所化可逆性は、同じ有限第一行の商比較と同値。
方針：同じ可換四角形の両制限が可逆であることを元の anodyne 局所化で使う。
規約：第一行商比較の証明・存在は追加仮定にせず、この必要十分条件だけを述べる。
使われ方：K-6 c5 の Sp 供給待ちを元の具体的比較へ代入する。 -/
theorem relativeSQuotient_localized_isIso_iff_firstRow :
    IsIso (AnodyneHomotopy.anodyneQ.map (relativeSQuotientMap q n)) ↔
      IsIso (AnodyneHomotopy.anodyneQ.map (relativeFirstRowQuotient q n)) := by
  let Q := AnodyneHomotopy.anodyneQ.{u}
  have hr : IsIso (Q.map (relativeFirstRowRestriction q n)) :=
    map_isIso_of_trivialKanFibration Q (Localization.inverts Q anodyneExtensions) _
  have hc : IsIso (Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (firstRowRestriction n C.obj))) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration (firstRowRestriction n C.obj)).core.anodyneQ_isIso
  have he := congrArg Q.map (relativeFirstRowQuotient_square q n)
  rw [Q.map_comp, Q.map_comp] at he
  constructor
  · intro h
    have hm : IsIso (Q.map (relativeFirstRowRestriction q n) ≫
        Q.map (relativeFirstRowQuotient q n)) := by
      rw [he]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp hm
  · intro h
    have hm : IsIso (Q.map (relativeSQuotientMap q n) ≫
        Q.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (firstRowRestriction n C.obj))) := by
      rw [← he]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp hm

end SerrePositivity.KST.Fibration
