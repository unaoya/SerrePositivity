module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionUnits

/-!
概要：端点保存の水平作用を増大単体圏の順序和と同じ射で比較する。
方針：端点保存の忠実な包含へ忘却し、空からの射も含む全関手を比較する。
規約：非空の対象だけに制限せず、全増大単体圏上で示す。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の水平結合則。
Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Opposite MonoidalCategory
open AugmentedSimplexCategory

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：端点保存の単体圏から増大単体圏への忘却。
方針：広部分圏の包含と非空部分の包含を合成する。
規約：指定された射と対象を変えない。使われ方：Riehl–Verity Remark 3.3.8 の作用比較。 -/
def endpointAugmentedForget (P : MorphismProperty SimplexCategory) [P.IsMultiplicative] :
    WideSubcategory P ⥤ AugmentedSimplexCategory :=
  wideSubcategoryInclusion P ⋙ WithInitial.incl

/-- 概要：端点の忘却は忠実。
方針：構成済みの二つの忠実な包含を合成する。
規約：忠実性を未証明の仮定にしない。使われ方：Riehl–Verity Remark 3.3.8 の射の照合。 -/
instance endpointAugmentedForget_faithful (P : MorphismProperty SimplexCategory)
    [P.IsMultiplicative] : (endpointAugmentedForget P).Faithful := by
  dsimp [endpointAugmentedForget]
  infer_instance

/-- 概要：端点の忘却は対象も区別する。
方針：非空包含の単射性と広部分圏の対象の外延性を使う。
規約：同じ骨格を使う。使われ方：Riehl–Verity Remark 3.3.8 の関手等式の回収。 -/
lemma endpointAugmentedForget_obj_injective (P : MorphismProperty SimplexCategory)
    [P.IsMultiplicative] : Function.Injective (endpointAugmentedForget P).obj := by
  intro X Y h
  apply WideSubcategory.ext
  exact WithInitial.of.inj h

variable {I : Type u} [Category.{v} I]

/-- 概要：端点の忘却後の関手等式は元の関手等式を決める。
方針：対象の単射性と射の忠実性を合わせる。
規約：対象等式の輸送を含む。使われ方：HA Proposition 4.7.3.3 の水平結合則の照合。 -/
lemma endpointAugmentedForget_comp_injective (P : MorphismProperty SimplexCategory)
    [P.IsMultiplicative] {F G : I ⥤ WideSubcategory P}
    (h : F ⋙ endpointAugmentedForget P = G ⋙ endpointAugmentedForget P) : F = G := by
  refine CategoryTheory.Functor.ext
    (fun X => endpointAugmentedForget_obj_injective P (CategoryTheory.Functor.congr_obj h X)) ?_
  intro X Y f
  apply (endpointAugmentedForget P).map_injective
  simpa only [CategoryTheory.Functor.map_comp, eqToHom_map,
    CategoryTheory.Functor.comp_map, CategoryTheory.Functor.comp_obj] using
    CategoryTheory.Functor.congr_hom h f

/-- 概要：最大元保存の左作用は、忘却後に元の順序和と全関手で一致する。
方針：空と非空の間の射を場合分けし、右包含の自然性と順序和の関手性を使う。
規約：射の増大も含む。使われ方：Riehl–Verity Remark 3.3.8 の水平結合則。 -/
lemma topOrdinalAction_forget :
    topOrdinalAction ⋙ endpointAugmentedForget simplexPreservesTop =
      (𝟭 AugmentedSimplexCategory).prod (endpointAugmentedForget simplexPreservesTop) ⋙
        tensor AugmentedSimplexCategory := by
  refine CategoryTheory.Functor.ext (fun X => by rcases X with ⟨a, x⟩; cases a <;> rfl) ?_
  rintro ⟨a, x⟩ ⟨b, y⟩ ⟨f, g⟩
  cases a with
  | star => cases b with
    | star =>
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      change (𝟙 x.obj) ≫ g.hom = g.hom
      exact Category.id_comp _
    | of b =>
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      change inr' b x.obj ≫ tensorHomOf (𝟙 b) g.hom = g.hom ≫ inr' b y.obj
      simpa only [Category.id_comp] using simplexOrdinalSum_inr (𝟙 b) g.hom
  | of a => cases b with
    | star => exact PEmpty.elim f
    | of b =>
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      change tensorHomOf f (𝟙 x.obj) ≫ tensorHomOf (𝟙 b) g.hom = tensorHomOf f g.hom
      simpa only [simplexOrdinalSum, prod_comp_fst, prod_comp_snd,
        Category.id_comp, Category.comp_id] using
        (simplexOrdinalSum.map_comp (X := (a, x.obj)) (Y := (b, x.obj))
          (Z := (b, y.obj)) (f, 𝟙 x.obj) (𝟙 b, g.hom)).symm

/-- 概要：最小元保存の右作用も、忘却後に元の順序和と全関手で一致する。
方針：空の後置からの左包含と、非空の順序和の関手性を照合する。
規約：増大からの射を残す。使われ方：Riehl–Verity Remark 3.3.8 の水平結合則。 -/
lemma bottomOrdinalAction_forget :
    bottomOrdinalAction ⋙ endpointAugmentedForget simplexPreservesBottom =
      (endpointAugmentedForget simplexPreservesBottom).prod (𝟭 AugmentedSimplexCategory) ⋙
        tensor AugmentedSimplexCategory := by
  refine CategoryTheory.Functor.ext (fun X => by rcases X with ⟨x, a⟩; cases a <;> rfl) ?_
  rintro ⟨x, a⟩ ⟨y, b⟩ ⟨g, f⟩
  cases a with
  | star => cases b with
    | star =>
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      change g.hom ≫ 𝟙 y.obj = g.hom
      exact Category.comp_id _
    | of b =>
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
  | of a => cases b with
    | star => exact PEmpty.elim f
    | of b =>
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      change tensorHomOf g.hom (𝟙 a) ≫ tensorHomOf (𝟙 y.obj) f = tensorHomOf g.hom f
      simpa only [simplexOrdinalSum, prod_comp_fst, prod_comp_snd,
        Category.id_comp, Category.comp_id] using
        (simplexOrdinalSum.map_comp (X := (x.obj, a)) (Y := (y.obj, a))
          (Z := (y.obj, b)) (g.hom, 𝟙 a) (𝟙 y.obj, f)).symm

/-- 概要：左作用の忘却比較を任意の二つの関手に適用する。
方針：比較の実関手等式に前合成する。規約：全Iの射の自然性。
使われ方：HA Proposition 4.7.3.3 の三重合成の比較。 -/
lemma topOrdinalActionFunctor_forget (F : I ⥤ AugmentedSimplexCategory)
    (G : I ⥤ TopSimplexCategory) :
    (F.prod' G ⋙ topOrdinalAction) ⋙ endpointAugmentedForget simplexPreservesTop =
      F.prod' (G ⋙ endpointAugmentedForget simplexPreservesTop) ⋙
        tensor AugmentedSimplexCategory := by
  exact congrArg (fun K => F.prod' G ⋙ K) topOrdinalAction_forget

/-- 概要：右作用の忘却比較を任意の二つの関手に適用する。
方針：比較に前合成する。規約：同じ添字圏の全射を含む。
使われ方：HA Proposition 4.7.3.3 の三重合成の比較。 -/
lemma bottomOrdinalActionFunctor_forget (F : I ⥤ BottomSimplexCategory)
    (G : I ⥤ AugmentedSimplexCategory) :
    (F.prod' G ⋙ bottomOrdinalAction) ⋙ endpointAugmentedForget simplexPreservesBottom =
      (F ⋙ endpointAugmentedForget simplexPreservesBottom).prod' G ⋙
        tensor AugmentedSimplexCategory := by
  exact congrArg (fun K => F.prod' G ⋙ K) bottomOrdinalAction_forget

/-- 概要：最大元保存の二回の左作用の全結合則。
方針：忠実な包含へ忘却し、既存の順序和の全結合則を使う。
規約：空の作用も含む全関手の等式。使われ方：HA Proposition 4.7.3.3 の水平結合。 -/
lemma topOrdinalActionFunctor_assoc (F G : I ⥤ AugmentedSimplexCategory)
    (H : I ⥤ TopSimplexCategory) :
    ((F.prod' G ⋙ tensor AugmentedSimplexCategory).prod' H ⋙ topOrdinalAction) =
      (F.prod' (G.prod' H ⋙ topOrdinalAction) ⋙ topOrdinalAction) := by
  apply endpointAugmentedForget_comp_injective simplexPreservesTop
  rw [topOrdinalActionFunctor_forget, topOrdinalActionFunctor_forget,
    topOrdinalActionFunctor_forget]
  exact ordinalSumFunctor_assoc F G (H ⋙ endpointAugmentedForget simplexPreservesTop)

/-- 概要：最小元保存の二回の右作用の全結合則。
方針：同じ包含の忠実性と元の順序和の全結合則を使う。
規約：任意のIの全射を量化する。使われ方：HA Proposition 4.7.3.3 の水平結合。 -/
lemma bottomOrdinalActionFunctor_assoc (F : I ⥤ BottomSimplexCategory)
    (G H : I ⥤ AugmentedSimplexCategory) :
    ((F.prod' G ⋙ bottomOrdinalAction).prod' H ⋙ bottomOrdinalAction) =
      (F.prod' (G.prod' H ⋙ tensor AugmentedSimplexCategory) ⋙ bottomOrdinalAction) := by
  apply endpointAugmentedForget_comp_injective simplexPreservesBottom
  rw [bottomOrdinalActionFunctor_forget, bottomOrdinalActionFunctor_forget,
    bottomOrdinalActionFunctor_forget]
  exact ordinalSumFunctor_assoc (F ⋙ endpointAugmentedForget simplexPreservesBottom) G H

end SerrePositivity.InfinityCategories.HA.Monads
