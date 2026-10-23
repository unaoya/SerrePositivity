module
public import SerrePositivity.InfinityCategories.Stable.NestedCosliceIso
public import SerrePositivity.InfinityCategories.Core.JoinAssociatorMiddle

/-! # 余極限余錐の下の coslice の制限

概要：余極限余錐全体の下の coslice は元の図式の下の coslice へ trivial Kan fibration で写る。
方針：二重 coslice の同型を通じて始対象の coslice 射影に帰着する。
規約：値域の quasicategory 性は仮定しない。
使われ方：S4 の左押し出しの余極限頂点を忘れる比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：余錐全体の下の coslice から元の図式の coslice への制限。
方針：二重 coslice の同型の後で、固定した余錐の下からの射影を取る。
規約：余極限性を仮定せず定義する。
使われ方：余極限頂点を付け加えた図式の coslice の比較。 -/
def colimitCosliceRestriction {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) :
    sliceUnder c.val ⟶ sliceUnder p :=
  (nestedCosliceIso c).hom ≫ sliceUnderProjection
    (SSet.yonedaEquiv.symm (show (sliceUnder p) _⦋0⦌ from c))

/-- 概要：余錐が余極限なら、元の図式への coslice の制限は trivial Kan fibration。
方針：二重 coslice の同型と、余極限の始対象性から得る射影の充填性を合成する。
規約：値域に追加の仮定はない。
使われ方：左四角形の押し出し性から外側比較の充填性を得る。 -/
lemma colimitCosliceRestriction_trivialKanFibration {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (hc : IsColimitCone c) :
    TrivialKanFibration (colimitCosliceRestriction c) := by
  have hp := (isColimitCone_iff_trivialKanFibration c).mp hc
  exact ⟨trivialKanFibrations.comp_mem _ _ (MorphismProperty.rlp_of_isIso _ _) hp.mem⟩

/-- 概要：余錐全体からの coslice 制限を uncurry すると基底包含との前合成になる。
方針：二重 coslice の自然性と二度の uncurry の式を使い、中間因子を忘れる包含を計算する。
規約：A とその射 f は任意。使われ方：通常の図式の制限との厳密な比較。 -/
lemma colimitCosliceRestriction_uncurry {K X A : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) (f : A ⟶ sliceUnder c.val) :
    sliceUnderUncurry (f ≫ colimitCosliceRestriction c) =
      joinMap (joinInl K Δ[0]) (𝟙 A) ≫ sliceUnderUncurry f := by
  have he : f ≫ (nestedCosliceIso c).hom = nestedCosliceHomEquiv c A f := by
    simpa only [nestedCosliceIso, Category.comp_id] using
      (nestedCosliceHomEquiv_naturality c f (𝟙 (sliceUnder c.val))).symm
  rw [colimitCosliceRestriction, ← Category.assoc, he,
    ← sliceUnderUncurry_projection (nestedCosliceHomEquiv c A f), sliceUnderUncurry_precomp,
    nestedCosliceHomEquiv_doubleUncurry, ← Category.assoc, stableJoinAssociator_middle_inv]

/-- 概要：余極限 coslice の制限は X への頂点射影と可換。
方針：制限の uncurry の式を右因子に沿って制限する。
規約：余極限性は不要。使われ方：余錐の頂点を保つ比較。 -/
lemma colimitCosliceRestriction_projection {K X : SSet.{u}} {p : K ⟶ X} (c : JoinCocone p) :
    colimitCosliceRestriction c ≫ sliceUnderProjection p = sliceUnderProjection c.val := by
  have he := colimitCosliceRestriction_uncurry c (𝟙 (sliceUnder c.val))
  simp only [Category.id_comp] at he
  rw [← sliceUnderUncurry_projection, he, ← Category.assoc, joinInr_joinMap,
    Category.id_comp, sliceUnderUncurry_projection, Category.id_comp]

/-- 概要：余錐が余極限であることは全体から基底への coslice 制限の trivial Kan fibration 性と同値。
方針：二重 coslice の同型を通じて始対象の射影の特徴づけを両方向に使う。
規約：値域の quasicategory 性を仮定しない。
使われ方：余極限頂点の付加による制限の判定。 -/
lemma isColimitCone_iff_colimitCosliceRestriction {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCocone p) : IsColimitCone c ↔ TrivialKanFibration (colimitCosliceRestriction c) := by
  constructor
  · exact colimitCosliceRestriction_trivialKanFibration c
  · intro h
    apply (isColimitCone_iff_trivialKanFibration c).mpr
    constructor
    have hp := trivialKanFibrations.comp_mem (nestedCosliceIso c).inv
      (colimitCosliceRestriction c) (MorphismProperty.rlp_of_isIso _ _) h.mem
    simpa only [colimitCosliceRestriction, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp] using hp

end SerrePositivity.InfinityCategories
