module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalSumFunctor

/-!
概要：walking adjunction の混合Homの、増大単体圏による二つの水平合成。
方針：非空な順序和を端点保存の圏へ制限し、WithInitial.liftで空順序集合も含める。
規約：空順序集合の作用は同じ恒等関手。両変数の射を保つ実関手を作る。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の
Δ₊×Δ∞→Δ∞、Δ−∞×Δ₊→Δ−∞。Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory MonoidalCategory

namespace SerrePositivity.InfinityCategories.HA.Monads

open AugmentedSimplexCategory

/-- 概要：非空な順序集合を前に付ける最大元保存の実関手族。
方針：順序和の双関手と右因子の最大元保存を使う。
規約：左因子の射は任意。使われ方：Riehl–Verity Remark 3.3.8。 -/
def topOrdinalPrefix : SimplexCategory ⥤ TopSimplexCategory ⥤ TopSimplexCategory where
  obj x :=
    { obj Y := ⟨tensorObjOf x Y.obj⟩
      map g := ⟨tensorHomOf (𝟙 x) g.hom,
        simplexOrdinalSum_preservesTop _ _ g.property⟩
      map_id Y := by
        apply WideSubcategory.hom_ext
        exact simplexOrdinalSum.map_id (x, Y.obj)
      map_comp {X Y Z} f g := by
        apply WideSubcategory.hom_ext
        simpa only [simplexOrdinalSum, prod_comp_fst, prod_comp_snd, Category.id_comp,
          WideSubcategory.comp_def, NatTrans.comp_app] using
          simplexOrdinalSum.map_comp (X := (x, X.obj)) (Y := (x, Y.obj)) (Z := (x, Z.obj))
            (𝟙 x, f.hom) (𝟙 x, g.hom) }
  map {x y} f :=
    { app Y := ⟨tensorHomOf f (𝟙 Y.obj), simplexOrdinalSum_preservesTop _ _ rfl⟩
      naturality Y Z g := by
        apply WideSubcategory.hom_ext
        have h₁ := simplexOrdinalSum.map_comp
          (X := (x, Y.obj)) (Y := (x, Z.obj)) (Z := (y, Z.obj))
          (𝟙 x, g.hom) (f, 𝟙 Z.obj)
        have h₂ := simplexOrdinalSum.map_comp
          (X := (x, Y.obj)) (Y := (y, Y.obj)) (Z := (y, Z.obj))
          (f, 𝟙 Y.obj) (𝟙 y, g.hom)
        simp only [simplexOrdinalSum, prod_comp_fst, prod_comp_snd,
          Category.id_comp, Category.comp_id] at h₁ h₂
        exact h₁.symm.trans h₂ }
  map_id x := by
    apply NatTrans.ext
    funext Y
    apply WideSubcategory.hom_ext
    exact simplexOrdinalSum.map_id (x, Y.obj)
  map_comp {x y z} f g := by
    apply NatTrans.ext
    funext Y
    apply WideSubcategory.hom_ext
    simpa only [simplexOrdinalSum, prod_comp_fst, prod_comp_snd, Category.id_comp,
          WideSubcategory.comp_def, NatTrans.comp_app] using
      simplexOrdinalSum.map_comp (X := (x, Y.obj)) (Y := (y, Y.obj)) (Z := (z, Y.obj))
        (f, 𝟙 Y.obj) (g, 𝟙 Y.obj)

/-- 概要：恒等関手から非空前置の関手への自然な包含。
方針：順序和の右包含を使う。規約：同じ最大元保存の圏内の自然変換。
使われ方：Riehl–Verity Remark 3.3.8 の空の前置からの合成。 -/
def topOrdinalPrefixInclusion (x : SimplexCategory) :
    𝟭 TopSimplexCategory ⟶ topOrdinalPrefix.obj x where
  app Y := ⟨inr' x Y.obj, simplexOrdinalSum_inr_last x Y.obj⟩
  naturality Y Z g := by
    apply WideSubcategory.hom_ext
    simpa only [topOrdinalPrefix, Functor.id_map, WideSubcategory.comp_def,
      Category.id_comp] using (simplexOrdinalSum_inr (𝟙 x) g.hom).symm

/-- 概要：前置への包含は前置する順序集合の射とも可換。
方針：右包含の両変数の自然性。規約：全ての最大元保存の対象での等式。
使われ方：Riehl–Verity Remark 3.3.8 の増大への拡張。 -/
lemma topOrdinalPrefixInclusion_naturality {x y : SimplexCategory} (f : x ⟶ y) :
    topOrdinalPrefixInclusion x ≫ topOrdinalPrefix.map f = topOrdinalPrefixInclusion y := by
  apply NatTrans.ext
  funext Y
  apply WideSubcategory.hom_ext
  simpa only [topOrdinalPrefixInclusion, topOrdinalPrefix, NatTrans.comp_app,
    WideSubcategory.comp_def, Category.id_comp] using simplexOrdinalSum_inr f (𝟙 Y.obj)

/-- 概要：空順序集合を含む前置の実関手族。
方針：空からの自然包含でWithInitial.liftを適用する。
規約：空の作用は同じ恒等関手。使われ方：Riehl–Verity Remark 3.3.8 の左合成。 -/
def topOrdinalPrefixExtended :
    AugmentedSimplexCategory ⥤ TopSimplexCategory ⥤ TopSimplexCategory :=
  WithInitial.lift topOrdinalPrefix topOrdinalPrefixInclusion
    (fun _ _ f => topOrdinalPrefixInclusion_naturality f)

/-- 概要：増大単体圏から最大元保存の圏への左水平合成。
方針：構成した全関手族をuncurryする。規約：両変数の射も含む。
使われ方：Riehl–Verity Remark 3.3.8 のΔ₊×Δ∞→Δ∞。 -/
def topOrdinalAction : AugmentedSimplexCategory × TopSimplexCategory ⥤ TopSimplexCategory :=
  Functor.uncurry.obj topOrdinalPrefixExtended

/-- 概要：空順序集合の左水平合成は恒等関手。
方針：WithInitial.liftの指定頂点の定義。規約：関手の等式。
使われ方：Riehl–Verity Remark 3.3.8 の水平合成の単位。 -/
lemma topOrdinalPrefixExtended_empty :
    topOrdinalPrefixExtended.obj WithInitial.star = 𝟭 TopSimplexCategory := rfl

/-- 概要：非空な順序集合を後ろに付ける最小元保存の実関手族。
方針：順序和の左因子の最小元保存を使う。
規約：後置する射は任意。使われ方：Riehl–Verity Remark 3.3.8。 -/
def bottomOrdinalSuffix : SimplexCategory ⥤ BottomSimplexCategory ⥤ BottomSimplexCategory where
  obj x :=
    { obj Y := ⟨tensorObjOf Y.obj x⟩
      map g := ⟨tensorHomOf g.hom (𝟙 x),
        simplexOrdinalSum_preservesBottom _ _ g.property⟩
      map_id Y := by
        apply WideSubcategory.hom_ext
        exact simplexOrdinalSum.map_id (Y.obj, x)
      map_comp {X Y Z} f g := by
        apply WideSubcategory.hom_ext
        simpa only [simplexOrdinalSum, prod_comp_fst, prod_comp_snd, Category.id_comp,
          WideSubcategory.comp_def, NatTrans.comp_app] using
          simplexOrdinalSum.map_comp (X := (X.obj, x)) (Y := (Y.obj, x)) (Z := (Z.obj, x))
            (f.hom, 𝟙 x) (g.hom, 𝟙 x) }
  map {x y} f :=
    { app Y := ⟨tensorHomOf (𝟙 Y.obj) f, simplexOrdinalSum_preservesBottom _ _ rfl⟩
      naturality Y Z g := by
        apply WideSubcategory.hom_ext
        have h₁ := simplexOrdinalSum.map_comp
          (X := (Y.obj, x)) (Y := (Z.obj, x)) (Z := (Z.obj, y))
          (g.hom, 𝟙 x) (𝟙 Z.obj, f)
        have h₂ := simplexOrdinalSum.map_comp
          (X := (Y.obj, x)) (Y := (Y.obj, y)) (Z := (Z.obj, y))
          (𝟙 Y.obj, f) (g.hom, 𝟙 y)
        simp only [simplexOrdinalSum, prod_comp_fst, prod_comp_snd,
          Category.id_comp, Category.comp_id] at h₁ h₂
        exact h₁.symm.trans h₂ }
  map_id x := by
    apply NatTrans.ext
    funext Y
    apply WideSubcategory.hom_ext
    exact simplexOrdinalSum.map_id (Y.obj, x)
  map_comp {x y z} f g := by
    apply NatTrans.ext
    funext Y
    apply WideSubcategory.hom_ext
    simpa only [simplexOrdinalSum, prod_comp_fst, prod_comp_snd, Category.id_comp,
          WideSubcategory.comp_def, NatTrans.comp_app] using
      simplexOrdinalSum.map_comp (X := (Y.obj, x)) (Y := (Y.obj, y)) (Z := (Y.obj, z))
        (𝟙 Y.obj, f) (𝟙 Y.obj, g)

/-- 概要：恒等関手から非空後置の関手への自然な包含。
方針：順序和の左包含を使う。規約：同じ最小元保存の圏内で取る。
使われ方：Riehl–Verity Remark 3.3.8 の空の後置からの合成。 -/
def bottomOrdinalSuffixInclusion (x : SimplexCategory) :
    𝟭 BottomSimplexCategory ⟶ bottomOrdinalSuffix.obj x where
  app Y := ⟨inl' Y.obj x, simplexOrdinalSum_inl_zero Y.obj x⟩
  naturality Y Z g := by
    apply WideSubcategory.hom_ext
    simpa only [bottomOrdinalSuffix, Functor.id_map, WideSubcategory.comp_def,
      Category.id_comp] using (simplexOrdinalSum_inl g.hom (𝟙 x)).symm

/-- 概要：後置への包含は後置する順序集合の射とも可換。
方針：左包含の自然性を使う。規約：実自然変換の等式。
使われ方：Riehl–Verity Remark 3.3.8 の増大への拡張。 -/
lemma bottomOrdinalSuffixInclusion_naturality {x y : SimplexCategory} (f : x ⟶ y) :
    bottomOrdinalSuffixInclusion x ≫ bottomOrdinalSuffix.map f =
      bottomOrdinalSuffixInclusion y := by
  apply NatTrans.ext
  funext Y
  apply WideSubcategory.hom_ext
  simpa only [bottomOrdinalSuffixInclusion, bottomOrdinalSuffix, NatTrans.comp_app,
    WideSubcategory.comp_def, Category.id_comp] using simplexOrdinalSum_inl (𝟙 Y.obj) f

/-- 概要：空順序集合を含む後置の実関手族。
方針：左包含を使ってWithInitial.liftで拡張する。
規約：空の作用は恒等関手。使われ方：Riehl–Verity Remark 3.3.8 の右合成。 -/
def bottomOrdinalSuffixExtended :
    AugmentedSimplexCategory ⥤ BottomSimplexCategory ⥤ BottomSimplexCategory :=
  WithInitial.lift bottomOrdinalSuffix bottomOrdinalSuffixInclusion
    (fun _ _ f => bottomOrdinalSuffixInclusion_naturality f)

/-- 概要：最小元保存の圏への増大単体圏の右水平合成。
方針：後置の関手族の変数を交換してuncurryする。規約：二つの変数の元の向きを保つ。
使われ方：Riehl–Verity Remark 3.3.8 のΔ−∞×Δ₊→Δ−∞。 -/
def bottomOrdinalAction :
    BottomSimplexCategory × AugmentedSimplexCategory ⥤ BottomSimplexCategory :=
  Functor.uncurry.obj bottomOrdinalSuffixExtended.flip

/-- 概要：空順序集合の右水平合成は恒等関手。
方針：指定したWithInitialの頂点の定義。規約：同じ圏上の関手の等式。
使われ方：Riehl–Verity Remark 3.3.8 の水平合成の単位。 -/
lemma bottomOrdinalSuffixExtended_empty :
    bottomOrdinalSuffixExtended.obj WithInitial.star = 𝟭 BottomSimplexCategory := rfl

/-- 概要：最大元保存の圏を最小元保存の反対圏として表示する実同値。
方針：構成済みのGalois双対の反対と二重反対の同値を合成する。
規約：同じ有限順序集合を台に持つ。使われ方：Riehl–Verity Remark 3.3.8 の双対側の合成。 -/
def topToBottomOpEquivalence : TopSimplexCategory ≌ BottomSimplexCategoryᵒᵖ :=
  (endpointSimplexEquivalence.op.trans (opOpEquivalence TopSimplexCategory)).symm

/-- 概要：増大単体圏の反対から最小元保存の圏への左水平合成。
方針：最大元保存の左合成の反対を取り、Galois双対で両端を戻す。
規約：全関手の合成として構成する。使われ方：Riehl–Verity Remark 3.3.8 の双対側。 -/
def bottomOppositeOrdinalAction :
    AugmentedSimplexCategoryᵒᵖ × BottomSimplexCategory ⥤ BottomSimplexCategory :=
  (𝟭 AugmentedSimplexCategoryᵒᵖ).prod endpointSimplexEquivalence.functor ⋙
    (prodOpEquiv (C := AugmentedSimplexCategory) (D := TopSimplexCategory)).inverse ⋙
      topOrdinalAction.op ⋙ endpointSimplexEquivalence.inverse

/-- 概要：最大元保存の圏への増大単体圏の反対の右水平合成。
方針：最小元保存の右合成の反対をGalois双対で移す。
規約：元の二つの変数とその射を保つ。
使われ方：Riehl–Verity Remark 3.3.8 のΔ∞×Δ₊ᵒᵖ→Δ∞。 -/
def topOppositeOrdinalAction :
    TopSimplexCategory × AugmentedSimplexCategoryᵒᵖ ⥤ TopSimplexCategory :=
  topToBottomOpEquivalence.functor.prod (𝟭 AugmentedSimplexCategoryᵒᵖ) ⋙
    (prodOpEquiv (C := BottomSimplexCategory) (D := AugmentedSimplexCategory)).inverse ⋙
      bottomOrdinalAction.op ⋙ topToBottomOpEquivalence.inverse

end SerrePositivity.InfinityCategories.HA.Monads
