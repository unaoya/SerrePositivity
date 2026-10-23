module

public import SerrePositivity.InfinityCategories.F1.Coherent.CompositionReindex

/-!
概要：同時パラメーター付きの豊穣合成の coherent 単体の面・退化の自然性。
方針：対象と Hom の表示を揃え、二種類の最大座標の自然性を使う。
規約：切替ラベルと二つの Hom 単体を同じ添字写像で制限する。
使われ方：標準合成 prism を単体集合の射へ束ねる。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：Hom の自然性は標準対象へ正規化した等式から従う。
方針：標的 Hom の同型を右に合成して消去する。
規約：二値ラベルは引き戻したものを始域で使う。
使われ方：三対象の合成 simplex の型の移送を扱う共通部分。 -/
lemma coherentCompositionHom_naturality_of_normalized {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z A B : C} {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (m + 2))
    (hA : coherentCompositionObj X Y Z (t.comp α.toOrderHom) i = A)
    (hB : coherentCompositionObj X Y Z (t.comp α.toOrderHom) j = B)
    (hA' : coherentCompositionObj X Y Z t (PinchedHom.extendOrderHom α.toOrderHom i) = A)
    (hB' : coherentCompositionObj X Y Z t (PinchedHom.extendOrderHom α.toOrderHom j) = B)
    (h : thickeningExtendHom α i j ≫ coherentCompositionHom σ τ t
      (PinchedHom.extendOrderHom α.toOrderHom i) (PinchedHom.extendOrderHom α.toOrderHom j) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom hA' hB') =
      coherentCompositionHom ((SimplicialCategory.sHom X Y).map α.op σ)
        ((SimplicialCategory.sHom Y Z).map α.op τ) (t.comp α.toOrderHom) i j ≫
          eqToHom (congrArg₂ SimplicialCategory.sHom hA hB)) :
    (thickeningExtendHom α i j ≫ coherentCompositionHom σ τ t
      (PinchedHom.extendOrderHom α.toOrderHom i) (PinchedHom.extendOrderHom α.toOrderHom j)) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (coherentCompositionObj_extend X Y Z α t i) (coherentCompositionObj_extend X Y Z α t j)) =
      coherentCompositionHom ((SimplicialCategory.sHom X Y).map α.op σ)
        ((SimplicialCategory.sHom Y Z).map α.op τ) (t.comp α.toOrderHom) i j := by
  apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom hA hB))).1
  simpa only [Category.assoc, eqToHom_trans] using h

/-- 概要：通常の最大座標の自然性を Hom の端点の移送を含む形で表示する。
方針：thickening の Hom の作用を path の添字変換へ戻す。
規約：終点は追加した最後の頂点。
使われ方：合成 simplex の二番目の豊穣射の自然性。 -/
lemma thickeningExtend_pathLastMaximumMap {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (i : Fin (m + 1)) :
    (thickeningExtendHom.{u} α i.castSucc (Fin.last (m + 1)) ≫
      eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
        (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩)
        (PinchedHom.extendOrderHom_castSucc α.toOrderHom i)
        (PinchedHom.extendOrderHom_last α.toOrderHom))) ≫ pathLastMaximumMap (α.toOrderHom i) =
      pathLastMaximumMap i ≫ stdSimplex.map α := by
  dsimp only [thickeningExtendHom]
  rw [thickeningExtend_map_cast_last, pathLastMaximumMap_naturality]

/-- 概要：同時パラメーター付きの豊穣合成の coherent simplex は全ての面・退化と整合する。
方針：Hom の表示変更を消し、切替前と最後以前の二つの最大座標の自然性を使う。
規約：局所 Kan 性は不要。
使われ方：普遍輸送の比較 prism の単体的な構成。 -/
lemma coherentCompositionSimplex_naturality {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z : C} {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2) :
    (SimplicialNerve C).map (PinchedHom.extend α).op (coherentCompositionSimplex σ τ t) =
      coherentCompositionSimplex ((SimplicialCategory.sHom X Y).map α.op σ)
        ((SimplicialCategory.sHom Y Z).map α.op τ) (t.comp α.toOrderHom) := by
  apply EnrichedFunctor.ext SSet
    (fun i ↦ coherentCompositionObj_extend X Y Z α t i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change (thickeningExtendHom α i j ≫ coherentCompositionHom σ τ t
    (PinchedHom.extendOrderHom α.toOrderHom i) (PinchedHom.extendOrderHom α.toOrderHom j)) ≫
      eqToHom _ = coherentCompositionHom ((SimplicialCategory.sHom X Y).map α.op σ)
        ((SimplicialCategory.sHom Y Z).map α.op τ) (t.comp α.toOrderHom) i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    let hl := PinchedHom.extendOrderHom_last α.toOrderHom
    let hN := coherentCompositionObj_last X Y Z n t
    let hM := coherentCompositionObj_last X Y Z m (t.comp α.toOrderHom)
    apply coherentCompositionHom_naturality_of_normalized α σ τ t _ _ hM hM
      ((congrArg (coherentCompositionObj X Y Z t) hl).trans hN)
      ((congrArg (coherentCompositionObj X Y Z t) hl).trans hN)
    rw [coherentCompositionHom_transport σ τ t hl hl hN hN]
    simp only [coherentCompositionHom_last_last, comp_toUnit_assoc]
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := Path.le (P.obj 0)
    change m + 1 ≤ j.val at h
    have hj : j.val < m + 1 := j.isLt
    omega
  case cast.last i =>
    let hi := PinchedHom.extendOrderHom_castSucc α.toOrderHom i
    let hj := PinchedHom.extendOrderHom_last α.toOrderHom
    let hNj := coherentCompositionObj_last X Y Z n t
    let hMj := coherentCompositionObj_last X Y Z m (t.comp α.toOrderHom)
    by_cases hti : t (α.toOrderHom i) = 0
    · let hNi := coherentCompositionObj_zero X Y Z t (α.toOrderHom i) hti
      let hMi := coherentCompositionObj_zero X Y Z (t.comp α.toOrderHom) i hti
      apply coherentCompositionHom_naturality_of_normalized α σ τ t _ _ hMi hMj
        ((congrArg (coherentCompositionObj X Y Z t) hi).trans hNi)
        ((congrArg (coherentCompositionObj X Y Z t) hj).trans hNj)
      rw [coherentCompositionHom_transport σ τ t hi hj hNi hNj]
      simp only [coherentCompositionHom_zero_last σ τ t (α.toOrderHom i) hti,
        coherentCompositionHom_zero_last _ _ (t.comp α.toOrderHom) i hti]
      let δ := thickeningExtendHom α i.castSucc (Fin.last (m + 1)) ≫
        eqToHom (congrArg₂ (fun a b : Fin (n + 2) ↦ SimplicialCategory.sHom
          (⟨ULift.up a⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up b⟩) hi hj)
      change δ ≫ (lift _ _ ≫ eComp SSet X Y Z) = _
      have hc : δ ≫ (pathCutMaximumMap t hti _ ≫ SSet.yonedaEquiv.symm σ) =
          pathCutMaximumMap (t.comp α.toOrderHom) hti _ ≫
            SSet.yonedaEquiv.symm ((SimplicialCategory.sHom X Y).map α.op σ) := by
        rw [← Category.assoc, thickeningExtend_pathCutMaximumMap α t i hti _ _ hj,
          Category.assoc, SSet.yonedaEquiv_symm_naturality_left]
      have hl : δ ≫ (pathLastMaximumMap (α.toOrderHom i) ≫ SSet.yonedaEquiv.symm τ) =
          pathLastMaximumMap i ≫
            SSet.yonedaEquiv.symm ((SimplicialCategory.sHom Y Z).map α.op τ) := by
        rw [← Category.assoc, thickeningExtend_pathLastMaximumMap,
          Category.assoc, SSet.yonedaEquiv_symm_naturality_left]
      rw [← Category.assoc, comp_lift, hc, hl]
    · let hNi := coherentCompositionObj_one X Y Z t (α.toOrderHom i) hti
      let hMi := coherentCompositionObj_one X Y Z (t.comp α.toOrderHom) i hti
      apply coherentCompositionHom_naturality_of_normalized α σ τ t _ _ hMi hMj
        ((congrArg (coherentCompositionObj X Y Z t) hi).trans hNi)
        ((congrArg (coherentCompositionObj X Y Z t) hj).trans hNj)
      rw [coherentCompositionHom_transport σ τ t hi hj hNi hNj]
      simp only [coherentCompositionHom_one_last σ τ t (α.toOrderHom i) hti,
        coherentCompositionHom_one_last _ _ (t.comp α.toOrderHom) i hti]
      simp only [← Category.assoc]
      rw [thickeningExtend_pathLastMaximumMap,
        Category.assoc, SSet.yonedaEquiv_symm_naturality_left]
  case cast.cast i j =>
    let hi := PinchedHom.extendOrderHom_castSucc α.toOrderHom i
    let hj := PinchedHom.extendOrderHom_castSucc α.toOrderHom j
    by_cases hti : t (α.toOrderHom i) = 0 <;> by_cases htj : t (α.toOrderHom j) = 0
    · let hNi := coherentCompositionObj_zero X Y Z t (α.toOrderHom i) hti
      let hNj := coherentCompositionObj_zero X Y Z t (α.toOrderHom j) htj
      let hMi := coherentCompositionObj_zero X Y Z (t.comp α.toOrderHom) i hti
      let hMj := coherentCompositionObj_zero X Y Z (t.comp α.toOrderHom) j htj
      apply coherentCompositionHom_naturality_of_normalized α σ τ t _ _ hMi hMj
        ((congrArg (coherentCompositionObj X Y Z t) hi).trans hNi)
        ((congrArg (coherentCompositionObj X Y Z t) hj).trans hNj)
      rw [coherentCompositionHom_transport σ τ t hi hj hNi hNj]
      simp only [coherentCompositionHom_zero_zero σ τ t _ _ hti htj,
        coherentCompositionHom_zero_zero _ _ (t.comp α.toOrderHom) _ _ hti htj,
        comp_toUnit_assoc]
    · let hNi := coherentCompositionObj_zero X Y Z t (α.toOrderHom i) hti
      let hNj := coherentCompositionObj_one X Y Z t (α.toOrderHom j) htj
      let hMi := coherentCompositionObj_zero X Y Z (t.comp α.toOrderHom) i hti
      let hMj := coherentCompositionObj_one X Y Z (t.comp α.toOrderHom) j htj
      apply coherentCompositionHom_naturality_of_normalized α σ τ t _ _ hMi hMj
        ((congrArg (coherentCompositionObj X Y Z t) hi).trans hNi)
        ((congrArg (coherentCompositionObj X Y Z t) hj).trans hNj)
      rw [coherentCompositionHom_transport σ τ t hi hj hNi hNj]
      simp only [coherentCompositionHom_zero_one σ τ t _ _ hti htj,
        coherentCompositionHom_zero_one _ _ (t.comp α.toOrderHom) _ _ hti htj]
      simp only [← Category.assoc]
      rw [thickeningExtend_pathCutMaximumMap α t i hti _ _ hj,
        Category.assoc, SSet.yonedaEquiv_symm_naturality_left]
    · apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro P
      exact False.elim (pathCut_backward_false (t.comp α.toOrderHom) hti htj (P.obj 0))
    · let hNi := coherentCompositionObj_one X Y Z t (α.toOrderHom i) hti
      let hNj := coherentCompositionObj_one X Y Z t (α.toOrderHom j) htj
      let hMi := coherentCompositionObj_one X Y Z (t.comp α.toOrderHom) i hti
      let hMj := coherentCompositionObj_one X Y Z (t.comp α.toOrderHom) j htj
      apply coherentCompositionHom_naturality_of_normalized α σ τ t _ _ hMi hMj
        ((congrArg (coherentCompositionObj X Y Z t) hi).trans hNi)
        ((congrArg (coherentCompositionObj X Y Z t) hj).trans hNj)
      rw [coherentCompositionHom_transport σ τ t hi hj hNi hNj]
      simp only [coherentCompositionHom_one_one σ τ t _ _ hti htj,
        coherentCompositionHom_one_one _ _ (t.comp α.toOrderHom) _ _ hti htj,
        comp_toUnit_assoc]

end SerrePositivity.InfinityCategories
