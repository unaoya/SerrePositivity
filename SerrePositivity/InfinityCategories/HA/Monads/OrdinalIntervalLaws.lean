module

public import SerrePositivity.InfinityCategories.HA.Monads.OrdinalIntervalFunctor

/-!
概要：区間表示の逆関手を含む往復を、同じ骨格上の関手の等式にする。
方針：増大単体圏と両端点保存の圏の同型が対象等式の輸送であることを証明する。
規約：逆関手の選択に依存する未証明の一致を仮定しない。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の
walking adjunctionの水平合成の法則。Kerodon Remark 6.2.1.4（Tag 02EN）。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite

namespace SerrePositivity.InfinityCategories.HA.Monads

/-- 概要：増大単体圏の対象は点の個数から戻る。
方針：空と非空を分ける。規約：指定した骨格での等式。
使われ方：Riehl–Verity Remark 3.3.8 の区間の逆表示。 -/
@[simp] lemma augmentedOrdinalOfCard_card (X : AugmentedSimplexCategory) :
    augmentedOrdinalOfCard (augmentedOrdinalCard X) = X := by
  cases X <;> rfl

/-- 概要：増大単体圏の対象の個数は対象を区別する。
方針：個数からの回収の等式を使う。規約：対象の等式。
使われ方：Riehl–Verity Remark 3.3.8 の逆表示の対象。 -/
lemma augmentedOrdinalCard_injective : Function.Injective augmentedOrdinalCard := by
  intro X Y h
  simpa only [augmentedOrdinalOfCard_card] using congrArg augmentedOrdinalOfCard h

/-- 概要：増大単体圏の同型な対象は等しい。
方針：空との不可能な射を除き、単体圏の骨格性を使う。
規約：同型の存在を新たに仮定しない。使われ方：Riehl–Verity Remark 3.3.8。 -/
lemma augmentedIso_obj_eq {X Y : AugmentedSimplexCategory} (e : X ≅ Y) : X = Y := by
  cases X with
  | star => cases Y with
    | star => rfl
    | of y => exact PEmpty.elim e.inv
  | of x => cases Y with
    | star => exact PEmpty.elim e.hom
    | of y =>
      apply congrArg WithInitial.of
      apply SimplexCategory.skeletal
      exact ⟨{
        hom := e.hom
        inv := e.inv
        hom_inv_id := e.hom_inv_id
        inv_hom_id := e.inv_hom_id }⟩

/-- 概要：増大単体圏の同型の射は対象等式の輸送。
方針：対象を同じにして、単体圏の自己同型の一意性を使う。
規約：射そのものの等式。使われ方：Riehl–Verity Remark 3.3.8 の厳密な往復。 -/
lemma augmentedIso_hom_eqToHom {X Y : AugmentedSimplexCategory} (e : X ≅ Y) :
    e.hom = eqToHom (augmentedIso_obj_eq e) := by
  have h := augmentedIso_obj_eq e
  subst Y
  cases X with
  | star => exact Subsingleton.elim _ _
  | of x =>
    let i : x ≅ x := {
      hom := e.hom
      inv := e.inv
      hom_inv_id := e.hom_inv_id
      inv_hom_id := e.inv_hom_id }
    exact SimplexCategory.eq_id_of_isIso i.hom

/-- 概要：反対の増大単体圏も同じ骨格を持つ。
方針：同型の反対を戻す。規約：元の反対圏の対象等式。
使われ方：Riehl–Verity Remark 3.3.8 の区間表示の単位。 -/
lemma augmentedOpIso_obj_eq {X Y : AugmentedSimplexCategoryᵒᵖ} (e : X ≅ Y) : X = Y :=
  (congrArg op (augmentedIso_obj_eq e.unop)).symm

/-- 概要：反対の増大単体圏の同型も対象等式の輸送。
方針：反対を外して上の一意性を使う。規約：射の向きを保つ。
使われ方：Riehl–Verity Remark 3.3.8 の往復の関手等式。 -/
lemma augmentedOpIso_hom_eqToHom {X Y : AugmentedSimplexCategoryᵒᵖ} (e : X ≅ Y) :
    e.hom = eqToHom (augmentedOpIso_obj_eq e) := by
  apply Quiver.Hom.unop_inj
  simpa only [Iso.unop_hom, eqToHom_unop] using augmentedIso_hom_eqToHom e.unop

/-- 概要：両端点保存の区間圏の同型な対象は等しい。
方針：忘却した同型に単体圏の骨格性を使う。
規約：区間圏の対象等式。使われ方：Riehl–Verity Remark 3.3.8 の余単位。 -/
lemma intervalIso_obj_eq {X Y : IntervalSimplexCategory} (e : X ≅ Y) : X = Y := by
  apply WideSubcategory.ext
  exact SimplexCategory.skeletal
    ⟨(wideSubcategoryInclusion simplexPreservesEndpoints).mapIso e⟩

/-- 概要：区間圏の同型の射は対象等式の輸送。
方針：忘却が忠実で、単体圏の自己同型が恒等射であることを使う。
規約：全区間での射の等式。使われ方：Riehl–Verity Remark 3.3.8 の厳密な往復。 -/
lemma intervalIso_hom_eqToHom {X Y : IntervalSimplexCategory} (e : X ≅ Y) :
    e.hom = eqToHom (intervalIso_obj_eq e) := by
  have h := intervalIso_obj_eq e
  subst Y
  apply WideSubcategory.hom_ext
  exact SimplexCategory.eq_id_of_isIso
    ((wideSubcategoryInclusion simplexPreservesEndpoints).mapIso e).hom

/-- 概要：区間表示を往復する関手は元の増大単体圏の反対の恒等関手。
方針：実同値の単位を対象等式による輸送と照合する。
規約：自然同型だけでなく全関手の等式。使われ方：HA Proposition 4.7.3.3 の水平合成則。 -/
lemma ordinalInterval_source_roundtrip :
    ordinalIntervalRepresentation ⋙ ordinalIntervalEquivalence.inverse =
      𝟭 AugmentedSimplexCategoryᵒᵖ := by
  exact Functor.ext_of_iso ordinalIntervalEquivalence.unitIso.symm
    (fun X => augmentedOpIso_obj_eq (ordinalIntervalEquivalence.unitIso.symm.app X))
    (fun X => augmentedOpIso_hom_eqToHom (ordinalIntervalEquivalence.unitIso.symm.app X))

/-- 概要：逆区間表示を往復する関手は元の区間圏の恒等関手。
方針：実同値の余単位を対象等式による輸送と照合する。
規約：射の全自然性を含む関手等式。使われ方：HA Proposition 4.7.3.3 の水平合成則。 -/
lemma ordinalInterval_target_roundtrip :
    ordinalIntervalEquivalence.inverse ⋙ ordinalIntervalRepresentation =
      𝟭 IntervalSimplexCategory := by
  exact Functor.ext_of_iso ordinalIntervalEquivalence.counitIso
    (fun X => intervalIso_obj_eq (ordinalIntervalEquivalence.counitIso.app X))
    (fun X => intervalIso_hom_eqToHom (ordinalIntervalEquivalence.counitIso.app X))

/-- 概要：逆区間表示の対象の点の個数は区間の次元。
方針：余単位の対象等式に次元を適用する。
規約：一点区間も含む。使われ方：Riehl–Verity Remark 3.3.8 の合成の対象計算。 -/
lemma ordinalInterval_inverse_card (X : IntervalSimplexCategory) :
    augmentedOrdinalCard (ordinalIntervalEquivalence.inverse.obj X).unop = X.obj.len := by
  exact congrArg (fun Y : IntervalSimplexCategory => Y.obj.len)
    (intervalIso_obj_eq (ordinalIntervalEquivalence.counitIso.app X))

/-- 概要：選択した逆関手の対象は個数から定める正準の対象に等しい。
方針：点の個数の単射性を使う。規約：逆関手の選択を外部仮定にしない。
使われ方：Riehl–Verity Remark 3.3.8 の合成の全対象等式。 -/
lemma ordinalInterval_inverse_obj (X : IntervalSimplexCategory) :
    ordinalIntervalEquivalence.inverse.obj X = op (augmentedOrdinalOfCard X.obj.len) := by
  apply unop_injective
  apply augmentedOrdinalCard_injective
  rw [augmentedOrdinalCard_ofCard]
  exact ordinalInterval_inverse_card X

/-- 概要：最小元保存・最大元保存の混合合成の個数。
方針：区間表示の逆の個数を、順序和の次元に帰着する。
規約：一方が零次元の場合も含む。使われ方：Riehl–Verity Remark 3.3.8 の水平合成。 -/
lemma mixedBottomTopOrdinal_card (X : BottomSimplexCategory) (Y : TopSimplexCategory) :
    augmentedOrdinalCard (mixedBottomTopOrdinal.obj (X, Y)).unop =
      X.obj.len + Y.obj.len + 1 := by
  exact ordinalInterval_inverse_card (bottomTopIntervalSum.obj (X, Y))

/-- 概要：最小元保存・最大元保存の混合合成の正準の対象。
方針：個数の単射性から対象等式を得る。規約：反対圏の同じ対象。
使われ方：HA Proposition 4.7.3.3 の合成の対象の検収。 -/
lemma mixedBottomTopOrdinal_obj (X : BottomSimplexCategory) (Y : TopSimplexCategory) :
    mixedBottomTopOrdinal.obj (X, Y) =
      op (augmentedOrdinalOfCard (X.obj.len + Y.obj.len + 1)) := by
  apply unop_injective
  apply augmentedOrdinalCard_injective
  rw [augmentedOrdinalCard_ofCard]
  exact mixedBottomTopOrdinal_card X Y

/-- 概要：最大元保存・最小元保存の逆順の混合合成の個数。
方針：Galois双対は対象を変えず、区間表示の逆の個数を使う。
規約：元の二つの変数の順序。使われ方：Riehl–Verity Remark 3.3.8 の水平合成。 -/
lemma mixedTopBottomOrdinal_card (X : TopSimplexCategory) (Y : BottomSimplexCategory) :
    augmentedOrdinalCard (mixedTopBottomOrdinal.obj (X, Y)) =
      X.obj.len + Y.obj.len + 1 := by
  exact ordinalInterval_inverse_card _

/-- 概要：逆順の混合合成も正準の個数の対象に等しい。
方針：点の個数が対象を区別することを使う。
規約：単位・結合則での対象の輸送を明示する。使われ方：HA Proposition 4.7.3.3。 -/
lemma mixedTopBottomOrdinal_obj (X : TopSimplexCategory) (Y : BottomSimplexCategory) :
    mixedTopBottomOrdinal.obj (X, Y) =
      augmentedOrdinalOfCard (X.obj.len + Y.obj.len + 1) := by
  apply augmentedOrdinalCard_injective
  rw [augmentedOrdinalCard_ofCard]
  exact mixedTopBottomOrdinal_card X Y

end SerrePositivity.InfinityCategories.HA.Monads
