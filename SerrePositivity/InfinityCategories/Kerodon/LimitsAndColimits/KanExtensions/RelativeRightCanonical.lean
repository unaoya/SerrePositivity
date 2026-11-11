module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeCoconeOpposite
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeLeftCanonical
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LocalCanonicalConeOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction

/-!
概要：元の右 Kan 関手の標準局所相対極限条件と左側の反転条件の同定。
方針：通常の錐の相対極限を反転し、局所添字の同型で標準右錐へ正規化する。
規約：右側の条件は通常の標準右 Kan 錐で定義する。
使われ方：元の相対左 Kan 制限定理を右の関手の全部分圏へ移す。

対応節は Kerodon 7.3（Tag 02Y1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions

/-- 概要：元の関手が δ から相対右 Kan 拡張されている標準局所条件。
方針：各頂点の標準右錐に U 相対極限性を課す。
規約：δ は任意の単体集合の射。
使われ方：元の関手圏内の右 Kan 関手の全部分複体の頂点条件。 -/
def IsRelativeRightKanExtendedFrom {K C D E : SSet.{u}}
    (U : D ⟶ E) (δ : K ⟶ C) (F : C ⟶ D) : Prop :=
  ∀ c : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone δ F c)

/-- 概要：同型な添字への制限は標準相対極限錐の条件を保ち反映する。
方針：slice の制限の両側の同型と後合成自然性で相対終対象性を移す。
規約：U の充填性や添字の quasicategory 性は不要。
使われ方：反転した標準錐の局所添字の正規化。 -/
lemma kanIsRelativeLimitCone_iff_restrict_of_isIso {A K D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) {p : K ⟶ D}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (i : A ⟶ K) [IsIso i] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone U c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone U
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p i).app (Opposite.op ⦋0⦌) c) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_isIso p i
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_isIso (p ≫ U) i
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeTerminalVertex_iff_of_iso_square
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp p U) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverPostcomp (i ≫ p) U)
    (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p i)) (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict (p ≫ U) i))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_postcomp p i U).symm c

/-- 概要：図式と錐全体が等しければ標準相対極限条件も等しい。
方針：図式の等式を消去し、錐の部分型の外延性を使う。
規約：錐の頂点だけでなく全体の射を比較する。
使われ方：反転と添字変更の後の図式の表示を揃える。 -/
lemma kanIsRelativeLimitCone_congr {A D E : SSet.{u}} (U : D ⟶ E)
    {p q : A ⟶ D} (hpq : p = q) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone q) (hcd : c.val = d.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone U c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone U d := by
  subst q
  have he : c = d := Subtype.ext hcd
  rw [he]

/-- 概要：標準左 Kan 余錐の相対余極限性は反転後の標準右錐の相対極限性と同値。
方針：余錐を反転し、局所添字の同型に制限して標準右錐と同定する。
規約：元の標準余錐と反転した元の関手の標準錐そのものを比較する。
使われ方：元の左右相対 Kan 条件の点ごとの双対化。 -/
lemma kanLeftCanonical_relativeColimit_iff_op_rightLimit {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C) (F : C ⟶ D)
    (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeLimitCone (SSet.opFunctor.map U)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (SSet.opFunctor.map δ) (SSet.opFunctor.map F)
          (SSet.opObjEquiv.symm c)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeOpIso δ c
  let p := SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ (δ ≫ F) c)
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c)
  let d := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p e.inv).app (Opposite.op ⦋0⦌) a
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsRelativeColimitCone_iff_reverseCone U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanCanonicalCocone δ F c)).trans
    (kanIsRelativeLimitCone_iff_restrict_of_isIso (SSet.opFunctor.map U) a e.inv)
  have hp : e.inv ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (SSet.opFunctor.map δ)
      (SSet.opFunctor.map δ ≫ SSet.opFunctor.map F) (SSet.opObjEquiv.symm c) := by
    dsimp only [e, p, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram]
    simp only [Functor.map_comp]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeOpIso_projection]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have hd : d.val = (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanCanonicalCone (SSet.opFunctor.map δ) (SSet.opFunctor.map F)
      (SSet.opObjEquiv.symm c)).val := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) e.inv ≫ a.val = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeReverseCone_val]
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalConeOppositeIso_canonical δ F c]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLocalConeOppositeIso, Iso.trans_inv, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso, e]
    simp only [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, Category.id_comp, Category.comp_id]
  exact h.trans (kanIsRelativeLimitCone_congr (SSet.opFunctor.map U) hp d _ hd)

/-- 概要：元の相対左 Kan 条件は反転した元の相対右 Kan 条件と同値。
方針：標準局所錐の双対判定を各頂点へ適用する。
規約：δ の単射性や U の inner 性は不要。
使われ方：元の関手の左右の全部分圏を反転で比較する。 -/
lemma kanIsRelativeLeftKanExtendedFrom_iff_op_right {K C D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) (δ : K ⟶ C) (F : C ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.IsRelativeLeftKanExtendedFrom U δ F ↔
      IsRelativeRightKanExtendedFrom (SSet.opFunctor.map U) (SSet.opFunctor.map δ)
        (SSet.opFunctor.map F) := by
  constructor
  · intro h c
    obtain ⟨b, rfl⟩ := (SSet.opObjEquiv (X := C) (n := Opposite.op ⦋0⦌)).symm.surjective c
    exact (kanLeftCanonical_relativeColimit_iff_op_rightLimit U δ F b).1 (h b)
  · intro h c
    exact (kanLeftCanonical_relativeColimit_iff_op_rightLimit U δ F c).2
      (h (SSet.opObjEquiv.symm c))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
