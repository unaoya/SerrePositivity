module

public import SerrePositivity.InfinityCategories.HA.Monads.AugmentedOrdinalMaps
public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalIntervalHom
public import SerrePositivity.InfinityCategories.HA.Monads.EndpointSimplex
public import SerrePositivity.InfinityCategories.HA.Monads.EndpointOrdinalActions
public import Mathlib.CategoryTheory.Equivalence

/-!
概要：増大単体圏の反対と、両端点保存の単体圏の実同値。
方針：証明済みの有限順序射の全単射・反変合成を実関手にまとめ、同じ対象の個数で回収する。
規約：空の順序集合は一点区間に写る。射の全単射をinstanceとして仮定しない。
使われ方：HA Proposition 4.7.3.3 のwalking adjunctionの混合Hom同士の合成。
Riehl–Verity Remark 3.3.8 の区間表示、Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：単体圏の射の両端点の保存。
方針：最小元と最大元の条件を合わせる。規約：一点区間も含む。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示の値域。 -/
def simplexPreservesEndpoints : MorphismProperty SimplexCategory :=
  fun _ _ f => simplexPreservesBottom f ∧ simplexPreservesTop f

/-- 概要：両端点の保存は恒等射・合成で保たれる。
方針：各端点の保存の構成済みの法則を使う。規約：同じ単体圏内。
使われ方：Riehl–Verity Remark 3.3.8 の区間の実圏。 -/
instance simplexPreservesEndpoints_multiplicative :
    simplexPreservesEndpoints.IsMultiplicative where
  id_mem _ := ⟨rfl, rfl⟩
  comp_mem f g hf hg :=
    ⟨simplexPreservesBottom.comp_mem f g hf.1 hg.1,
      simplexPreservesTop.comp_mem f g hf.2 hg.2⟩

/-- 概要：両端点を保つ有限区間の射の実圏。
方針：単体圏の広部分圏を取る。規約：対象は非空有限区間の全て。
使われ方：Riehl–Verity Remark 3.3.8 のirの因子。 -/
abbrev IntervalSimplexCategory := WideSubcategory simplexPreservesEndpoints

/-- 概要：増大単体圏の反対から両端点保存の圏への実区間表示。
方針：点の個数を一つ増やし、有限順序射の実区間表示を使う。
規約：空の対象も含む全関手。使われ方：Riehl–Verity Remark 3.3.8 のir。 -/
def ordinalIntervalRepresentation : AugmentedSimplexCategoryᵒᵖ ⥤ IntervalSimplexCategory where
  obj X := ⟨SimplexCategory.mk (augmentedOrdinalCard X.unop)⟩
  map f :=
    ⟨SimplexCategory.Hom.mk (ordinalIntervalMap (augmentedOrderHom f.unop)),
      ordinalIntervalMap_zero _, ordinalIntervalMap_last _⟩
  map_id X := by
    apply WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext'
    change ordinalIntervalMap (augmentedOrderHom (𝟙 X.unop)) = OrderHom.id
    rw [augmentedOrderHom_id, ordinalIntervalMap_id]
  map_comp f g := by
    apply WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext'
    change ordinalIntervalMap (augmentedOrderHom (g.unop ≫ f.unop)) =
      (ordinalIntervalMap (augmentedOrderHom g.unop)).comp
        (ordinalIntervalMap (augmentedOrderHom f.unop))
    rw [augmentedOrderHom_comp, ordinalIntervalMap_comp]

/-- 概要：実区間表示は忠実。
方針：構成した二つのHomの全単射の単射性を使う。
規約：元の増大単体圏の反対の射の等式を戻す。使われ方：Riehl–Verity Remark 3.3.8。 -/
instance ordinalIntervalRepresentation_faithful : ordinalIntervalRepresentation.Faithful where
  map_injective {X Y} f g h := by
    apply Quiver.Hom.unop_inj
    apply (augmentedOrderHomEquiv Y.unop X.unop).injective
    apply (ordinalIntervalHomEquiv _ _).injective
    apply Subtype.ext
    exact congrArg (fun k => k.hom.toOrderHom) h

/-- 概要：実区間表示は両端点保存の射に関して充満。
方針：区間射から有限順序射を実際に回収し、元の増大単体圏の射へ戻す。
規約：全射性を未証明のinstanceとして入力しない。使われ方：Riehl–Verity Remark 3.3.8。 -/
instance ordinalIntervalRepresentation_full : ordinalIntervalRepresentation.Full where
  map_surjective {X Y} h := by
    let l : {l : Fin (augmentedOrdinalCard X.unop + 1) →o
        Fin (augmentedOrdinalCard Y.unop + 1) //
        l 0 = 0 ∧ l (Fin.last (augmentedOrdinalCard X.unop)) =
          Fin.last (augmentedOrdinalCard Y.unop)} := ⟨h.hom.toOrderHom, h.property⟩
    let q := (ordinalIntervalHomEquiv _ _).symm l
    let g := (augmentedOrderHomEquiv Y.unop X.unop).symm q
    refine ⟨g.op, ?_⟩
    apply WideSubcategory.hom_ext
    apply SimplexCategory.Hom.ext'
    change ordinalIntervalMap (augmentedOrderHom g) = h.hom.toOrderHom
    have hg : augmentedOrderHom g = q :=
      (augmentedOrderHomEquiv Y.unop X.unop).apply_symm_apply q
    rw [hg]
    exact congrArg Subtype.val ((ordinalIntervalHomEquiv _ _).apply_symm_apply l)

/-- 概要：実区間表示の値は全ての有限区間を覆う。
方針：区間の次元と同じ点の個数を持つ増大単体圏の対象を作る。
規約：一点区間の原像は空の対象。使われ方：Riehl–Verity Remark 3.3.8 の逆関手。 -/
instance ordinalIntervalRepresentation_essSurj : ordinalIntervalRepresentation.EssSurj where
  mem_essImage Y := by
    refine ⟨op (augmentedOrdinalOfCard Y.obj.len), ⟨eqToIso ?_⟩⟩
    apply WideSubcategory.ext
    apply SimplexCategory.ext
    exact augmentedOrdinalCard_ofCard Y.obj.len

/-- 概要：区間表示の実関手は同値。
方針：上で証明した忠実性・充満性・本質的全射性をまとめる。
規約：同値性を引数の仮定に置かない。使われ方：Riehl–Verity Remark 3.3.8。 -/
instance ordinalIntervalRepresentation_isEquivalence :
    ordinalIntervalRepresentation.IsEquivalence where

/-- 概要：増大単体圏の反対と両端点保存の区間圏の実同値。
方針：証明済みの実関手の同値性から逆・単位・余単位を構成する。
規約：片方向のHom表示だけで終えない。使われ方：HA Proposition 4.7.3.3 の水平合成の因子。 -/
def ordinalIntervalEquivalence : AugmentedSimplexCategoryᵒᵖ ≌ IntervalSimplexCategory :=
  ordinalIntervalRepresentation.asEquivalence

/-- 概要：最小元保存の射と最大元保存の射の順序和は両端点保存の射になる。
方針：構成済みの順序和の両側の端点保存則を合わせる。
規約：両変数の射を含む実双関手。使われ方：Riehl–Verity Remark 3.3.8 の因子化。 -/
def bottomTopIntervalSum :
    BottomSimplexCategory × TopSimplexCategory ⥤ IntervalSimplexCategory where
  obj X := ⟨AugmentedSimplexCategory.tensorObjOf X.1.obj X.2.obj⟩
  map f :=
    ⟨AugmentedSimplexCategory.tensorHomOf f.1.hom f.2.hom,
      simplexOrdinalSum_preservesBottom _ _ f.1.property,
      simplexOrdinalSum_preservesTop _ _ f.2.property⟩
  map_id X := by
    apply WideSubcategory.hom_ext
    exact simplexOrdinalSum.map_id (X.1.obj, X.2.obj)
  map_comp {X Y Z} f g := by
    apply WideSubcategory.hom_ext
    simpa only [simplexOrdinalSum, prod_comp_fst, prod_comp_snd,
      WideSubcategory.comp_def] using
      simplexOrdinalSum.map_comp
        (X := (X.1.obj, X.2.obj)) (Y := (Y.1.obj, Y.2.obj)) (Z := (Z.1.obj, Z.2.obj))
        (f.1.hom, f.2.hom) (g.1.hom, g.2.hom)

/-- 概要：二つの混合Homの合成を増大単体圏の反対へ戻す実双関手。
方針：両端点保存の順序和と、実区間同値の逆関手を合成する。
規約：元の射の向きを保持する。使われ方：Riehl–Verity Remark 3.3.8 の混合水平合成。 -/
def mixedBottomTopOrdinal :
    BottomSimplexCategory × TopSimplexCategory ⥤ AugmentedSimplexCategoryᵒᵖ :=
  bottomTopIntervalSum ⋙ ordinalIntervalEquivalence.inverse

/-- 概要：逆順の二つの混合Homの合成を増大単体圏へ送る実双関手。
方針：Galois双対・反対圏と実区間同値を合成する。
規約：二重反対を元の増大単体圏へ明示的に戻す。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の残る混合水平合成。 -/
def mixedTopBottomOrdinal :
    TopSimplexCategory × BottomSimplexCategory ⥤ AugmentedSimplexCategory :=
  topToBottomOpEquivalence.functor.prod endpointSimplexEquivalence.functor ⋙
    (prodOpEquiv (C := BottomSimplexCategory) (D := TopSimplexCategory)).inverse ⋙
      bottomTopIntervalSum.op ⋙ ordinalIntervalEquivalence.inverse.op ⋙
        (opOpEquivalence AugmentedSimplexCategory).functor

end SerrePositivity.InfinityCategories.HA.Monads
