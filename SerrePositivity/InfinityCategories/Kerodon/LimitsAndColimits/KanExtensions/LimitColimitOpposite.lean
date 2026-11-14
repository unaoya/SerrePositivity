module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeOpposite
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.HA.Section6_1_1.SquareDuality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanShapeCommaProjection

/-!
概要：局所 Kan 図式の余極限と反転後の局所極限の存在を比較する。
方針：slice の反転同型で普遍錐を移し、局所添字の同型に沿って制限する。
規約：quasicategory 性を仮定しない存在条件の比較。
使われ方：左 Kan 拡張の存在定理を右側へ双対化する。

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

/-- 概要：図式の極限の存在は反転した図式の余極限の存在と同値。
方針：slice の反転同型を頂点に適用し、終対象と始対象の反転を使う。
規約：図式と標的は任意。
使われ方：点ごとの極限・余極限の存在の双対化。 -/
lemma kanHasLimit_iff_hasColimit_op {A D : SSet.{u}} (p : A ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (SSet.opFunctor.map p) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c.reverseCocone, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isLimitCone_iff_reverseCocone c).1 hc⟩
  · rintro ⟨d, hd⟩
    let x := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpIso p).inv.app (Opposite.op ⦋0⦌) d
    let c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone p := SSet.opObjEquiv x
    refine ⟨c, ?_⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isTerminalVertex_iff_isInitialVertex_op (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver p) c).2
    exact hd.map_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverOpIso p).inv

/-- 概要：同型な添字への制限は極限の存在を保ち反映する。
方針：slice の制限同型を頂点へ適用する。
規約：標的の充填性は不要。
使われ方：反転した標準局所図式の添字の正規化。 -/
lemma kanHasLimit_iff_restrict_of_isIso {A B D : SSet.{u}}
    (p : B ⟶ D) (f : A ⟶ B) [IsIso f] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (f ≫ p) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_isIso p f
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p f).app (Opposite.op ⦋0⦌) c,
      hc.map_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p f)⟩
  · rintro ⟨c, hc⟩
    exact ⟨(inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p f)).app (Opposite.op ⦋0⦌) c,
      hc.map_of_isIso (inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p f))⟩

/-- 概要：同型な添字への制限は余極限の存在を保ち反映する。
方針：coslice の制限同型とその逆で始対象を写す。
規約：標的の充填性は不要。
使われ方：二重反転した図式の添字を戻す。 -/
lemma kanHasColimit_iff_restrict_of_isIso {A B D : SSet.{u}}
    (p : B ⟶ D) (f : A ⟶ B) [IsIso f] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (f ≫ p) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p f).app (Opposite.op ⦋0⦌) c,
      hc.map_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p f)⟩
  · rintro ⟨c, hc⟩
    exact ⟨(inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p f)).app (Opposite.op ⦋0⦌) c,
      hc.map_of_isIso (inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p f))⟩

/-- 概要：標的の同型への後合成は余極限の存在を保ち反映する。
方針：後合成による coslice の同型を使う。
規約：同型の指定以外に仮定を置かない。
使われ方：二重反転した図式の標的を戻す。 -/
lemma kanHasColimit_iff_postcomp_of_isIso {A D E : SSet.{u}}
    (p : A ⟶ D) (f : D ⟶ E) [IsIso f] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (p ≫ f) := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p f).app (Opposite.op ⦋0⦌) c,
      hc.map_of_isIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p f)⟩
  · rintro ⟨c, hc⟩
    exact ⟨(inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p f)).app (Opposite.op ⦋0⦌) c,
      hc.map_of_isIso (inv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p f))⟩

/-- 概要：余極限の存在は反転した図式の極限の存在と同値。
方針：極限から余極限への反転をもう一度適用し、二重反転を同型で消去する。
規約：quasicategory 性は不要。
使われ方：左 Kan の局所存在条件を右側へ渡す。 -/
lemma kanHasColimit_iff_hasLimit_op {A D : SSet.{u}} (p : A ⟶ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (SSet.opFunctor.map p) := by
  have h := kanHasColimit_iff_postcomp_of_isIso
    (SSet.opFunctor.map (SSet.opFunctor.map p)) (SSet.opFunctorCompOpFunctorIso.app D).hom
  have hn := SSet.opFunctorCompOpFunctorIso.hom.naturality p
  change SSet.opFunctor.map (SSet.opFunctor.map p) ≫
    (SSet.opFunctorCompOpFunctorIso.app D).hom =
      (SSet.opFunctorCompOpFunctorIso.app A).hom ≫ p at hn
  rw [hn] at h
  exact ((kanHasColimit_iff_restrict_of_isIso p
    (SSet.opFunctorCompOpFunctorIso.app A).hom).trans h.symm).trans
      (kanHasLimit_iff_hasColimit_op (SSet.opFunctor.map p)).symm

/-- 概要：左 Kan の局所余極限の存在は反転した右 Kan の局所極限の存在と同値。
方針：局所添字の反転同型が保つ図式を計算して極限の存在を移す。
規約：関手と三つの単体集合は任意。
使われ方：左の存在定理の双対化の入力。 -/
lemma kanLocalColimit_iff_oppositeLocalLimit {K C D : SSet.{u}}
    (δ : K ⟶ C) (F₀ : K ⟶ D) (c : C _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
        (SSet.opObjEquiv.symm c)) := by
  have h := kanHasLimit_iff_restrict_of_isIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
      (SSet.opObjEquiv.symm c)) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeOpIso δ c).hom
  have hd : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeOpIso δ c).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram (SSet.opFunctor.map δ) (SSet.opFunctor.map F₀)
        (SSet.opObjEquiv.symm c) = SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanShapeOpIso_projection, CategoryTheory.Functor.map_comp]
  rw [hd] at h
  exact (kanHasColimit_iff_hasLimit_op (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ c)).trans h.symm

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
