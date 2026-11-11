module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Coslice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CoreJoinAssociator
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAssociatorMiddle
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.Terminal
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.NestedCosliceIso

/-! # 余極限余錐の下の coslice の制限

概要：余極限余錐全体の下の coslice は元の図式の下の coslice へ trivial Kan fibration で写る。
方針：二重 coslice の同型を通じて始対象の coslice 射影に帰着する。
規約：値域の quasicategory 性は仮定しない。
使われ方：S4 の左押し出しの余極限頂点を忘れる比較。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：余錐全体の下の coslice から元の図式の coslice への制限。
方針：二重 coslice の同型の後で、固定した余錐の下からの射影を取る。
規約：余極限性を仮定せず定義する。
使われ方：余極限頂点を付け加えた図式の coslice の比較。 -/
def colimitCosliceRestriction {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder c.val ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceIso c).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection
    (SSet.yonedaEquiv.symm (show (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p) _⦋0⦌ from c))

/-- 概要：余錐が余極限なら、元の図式への coslice の制限は trivial Kan fibration。
方針：二重 coslice の同型と、余極限の始対象性から得る射影の充填性を合成する。
規約：値域に追加の仮定はない。
使われ方：左四角形の押し出し性から外側比較の充填性を得る。 -/
lemma colimitCosliceRestriction_trivialKanFibration {K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (colimitCosliceRestriction c) := by
  have hp := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_trivialKanFibration c).mp hc
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem _ _ (MorphismProperty.rlp_of_isIso _ _) hp.mem⟩

/-- 概要：余錐全体からの coslice 制限を uncurry すると基底包含との前合成になる。
方針：二重 coslice の自然性と二度の uncurry の式を使い、中間因子を忘れる包含を計算する。
規約：A とその射 f は任意。使われ方：通常の図式の制限との厳密な比較。 -/
lemma colimitCosliceRestriction_uncurry {K X A : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder c.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (f ≫ colimitCosliceRestriction c) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0]) (𝟙 A) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f := by
  have he : f ≫ (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceIso c).hom = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceHomEquiv c A f := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceIso, Category.comp_id] using
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceHomEquiv_naturality c f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder c.val))).symm
  rw [colimitCosliceRestriction, ← Category.assoc, he,
    ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceHomEquiv c A f), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_precomp,
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceHomEquiv_doubleUncurry, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinAssociator_middle_inv]

/-- 概要：余極限 coslice の制限は X への頂点射影と可換。
方針：制限の uncurry の式を右因子に沿って制限する。
規約：余極限性は不要。使われ方：余錐の頂点を保つ比較。 -/
lemma colimitCosliceRestriction_projection {K X : SSet.{u}} {p : K ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    colimitCosliceRestriction c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection c.val := by
  have he := colimitCosliceRestriction_uncurry c (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder c.val))
  simp only [Category.id_comp] at he
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection, he, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap,
    Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderUncurry_projection, Category.id_comp]

/-- 概要：余錐が余極限であることは全体から基底への coslice 制限の trivial Kan fibration 性と同値。
方針：二重 coslice の同型を通じて始対象の射影の特徴づけを両方向に使う。
規約：値域の quasicategory 性を仮定しない。
使われ方：余極限頂点の付加による制限の判定。 -/
lemma isColimitCone_iff_colimitCosliceRestriction {K X : SSet.{u}} {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (colimitCosliceRestriction c) := by
  constructor
  · exact colimitCosliceRestriction_trivialKanFibration c
  · intro h
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_trivialKanFibration c).mpr
    constructor
    have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibrations.comp_mem (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.nestedCosliceIso c).inv
      (colimitCosliceRestriction c) (MorphismProperty.rlp_of_isIso _ _) h.mem
    simpa only [colimitCosliceRestriction, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp] using hp

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
