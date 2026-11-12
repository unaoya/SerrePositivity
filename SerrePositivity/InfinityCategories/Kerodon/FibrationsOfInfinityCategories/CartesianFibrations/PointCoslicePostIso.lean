module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ParametrizedTransportSquare
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IntervalCosliceSource

/-!
概要：底の同型による頂点の coslice の同型と普遍輸送の同値性の移送。
方針：錐の後合成の逆を直接作り、固定頂点の Yoneda 表示を正規化する。
規約：底の同型の両方向を厳密に使う。
使われ方：反対 Kan 圏の nerve 上の普遍輸送を pointed-space 射影へ戻す。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：標的の同型による coslice の後合成は同型。
方針：錐の射を逆同型で後合成して逆を作る。
規約：固定図式の始域は任意。
使われ方：普遍輸送の正方形の全空間の同型。 -/
def sliceUnderPostcompIso {K X Y : SSet.{u}} (p : K ⟶ X) (e : X ≅ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p ≅ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (p ≫ e.hom) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p e.hom
  inv := {
    app _ := ↾fun s ↦ ⟨s.val ≫ e.inv, by
      rw [← Category.assoc, s.property, Category.assoc, e.hom_inv_id, Category.comp_id]⟩
    naturality := by
      intro n m α
      apply ConcreteCategory.hom_ext
      intro s
      apply Subtype.ext
      exact Category.assoc _ _ _ }
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (s.val ≫ e.hom) ≫ e.inv = s.val
    rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  inv_hom_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change (s.val ≫ e.inv) ≫ e.hom = s.val
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]

/-- 概要：固定図式の等号で移した coslice は射影を保つ。
方針：図式の等号を消去する。
規約：底の単体集合は保つ。
使われ方：頂点の Yoneda 表示への正規化。 -/
lemma sliceUnder_eqToHom_projection {K X : SSet.{u}} {p q : K ⟶ X} (h : p = q) :
    eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p := by
  subst q
  simp

/-- 概要：底の同型は対応する頂点からの coslice の厳密な同型を与える。
方針：後合成の同型に固定頂点の Yoneda 表示変更を合成する。
規約：標的の頂点は同型の零単体での像。
使われ方：pointed-space 射影を含む正規化済みの全空間の同型。 -/
def pointCoslicePostIso {B D : SSet.{u}} (d : B ≅ D) (z : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm z) ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv.symm (d.hom.app _ z)) :=
  sliceUnderPostcompIso (SSet.yonedaEquiv.symm z) d ≪≫
    eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (SSet.yonedaEquiv_symm_comp z d.hom))

/-- 概要：頂点の coslice の後合成同型は底の同型を被覆する。
方針：固定図式の正規化を消し、後合成の射影の公式を使う。
規約：射影の厳密な可換正方形。
使われ方：普遍輸送の同値性の同型による移送。 -/
lemma pointCoslicePostIso_projection {B D : SSet.{u}} (d : B ≅ D) (z : B _⦋0⦌) :
    (pointCoslicePostIso d z).hom ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (d.hom.app _ z)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm z) ≫ d.hom := by
  dsimp only [pointCoslicePostIso, Iso.trans_hom, eqToIso.hom]
  rw [Category.assoc, sliceUnder_eqToHom_projection (SSet.yonedaEquiv_symm_comp z d.hom)]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.sliceUnderPostcomp_projection _ _

/-- 概要：底の同型で対応する頂点の coslice の普遍輸送は同値性を保つ。
方針：正規化済みの coslice の可換正方形に一般の移送定理を適用する。
規約：全写像空間から fiber 間の関手空間への実際の普遍輸送。
使われ方：pointed-space 射影への移送の最後の正方形。 -/
lemma parametrizedPointCosliceTransport_isQCatEquivalence_of_iso
    {B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (d : B ≅ D) (z a b : B _⦋0⦌)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm z)) a b)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm (d.hom.app _ z)))
      (d.hom.app _ a) (d.hom.app _ b)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.parametrizedFiberTransport_isQCatEquivalence_of_squareIso _ _ (pointCoslicePostIso d z) d
    (pointCoslicePostIso_projection d z) a b h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
