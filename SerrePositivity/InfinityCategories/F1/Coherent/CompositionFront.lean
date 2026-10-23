module

public import SerrePositivity.InfinityCategories.F1.Coherent.PrismCutCoordinates

/-!
概要：三対象の合成 simplex の前面を右 Hom 比較の切断制限として同定する。
方針：四つのラベルの場合で対象と Hom を正規化し、最大座標の像の公式を使う。
規約：第二の豊穣射の値は前面に影響しない。
使われ方：合成 prism の射影を既存の区間比較へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：右 Hom の切断した対象は合成図式の前面の対象と一致する。
方針：零ラベルと一ラベルで切断の値を計算する。
規約：合成図式の追加した最後の頂点は前面には含まない。
使われ方：前面の豊穣関手の対象部分の同定。 -/
lemma coherentCompositionObj_front {C : Type v} (X Y Z : C) {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) :
    coherentCompositionObj X Y Z t i.castSucc =
      coherentHomComparisonObj X Y (coherentPrismCut t i) := by
  by_cases hi : t i = 0
  · rw [coherentCompositionObj_zero X Y Z t i hi, coherentPrismCut_zero t i hi,
      coherentHomComparisonObj_cast]
  · rw [coherentCompositionObj_one X Y Z t i hi, coherentPrismCut_one t i hi,
      coherentHomComparisonObj_last]

/-- 概要：合成 simplex の前面は最初の射の右 Hom 比較を切断写像で制限したもの。
方針：二端点のラベルごとに Hom の表示を揃えて比較する。
規約：全ての高次 Hom の作用を含む coherent 単体の等式。
使われ方：合成 prism の射影の厳密な式。 -/
lemma coherentCompositionSimplex_front {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z : C} {n : ℕ} (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2) :
    (SimplicialNerve C).map (PinchedHom.front n).op (coherentCompositionSimplex σ τ t) =
      (SimplicialNerve C).map (SimplexCategory.mkHom (coherentPrismCut t)).op
        (coherentHomComparisonSimplex σ) := by
  apply EnrichedFunctor.ext SSet (fun i ↦ coherentCompositionObj_front X Y Z t i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change ((SimplicialThickening.functor (PinchedHom.front n).toOrderHom.uliftMap).map
    (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ≫
      coherentCompositionHom σ τ t i.castSucc j.castSucc) ≫ eqToHom _ =
    (SimplicialThickening.functor (coherentPrismCut t).uliftMap).map _ _ ≫
      coherentHomComparisonHom σ (coherentPrismCut t i) (coherentPrismCut t j)
  by_cases hi : t i = 0 <;> by_cases hj : t j = 0
  · let hAi := coherentHomComparisonObj_cast X Y i
    let hBj := coherentHomComparisonObj_cast X Y j
    let hi' := coherentPrismCut_zero t i hi
    let hj' := coherentPrismCut_zero t j hj
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg (coherentHomComparisonObj X Y) hi').trans hAi)
      ((congrArg (coherentHomComparisonObj X Y) hj').trans hBj)))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [coherentCompositionHom_zero_zero σ τ t i j hi hj,
      coherentHomComparisonHom_transport σ hi' hj' hAi hBj,
      coherentHomComparisonHom_cast_cast]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    rfl
  · let hAi := coherentHomComparisonObj_cast X Y i
    let hBj := coherentHomComparisonObj_last X Y n
    let hi' := coherentPrismCut_zero t i hi
    let hj' := coherentPrismCut_one t j hj
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg (coherentHomComparisonObj X Y) hi').trans hAi)
      ((congrArg (coherentHomComparisonObj X Y) hj').trans hBj)))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [coherentCompositionHom_zero_one σ τ t i j hi hj,
      coherentHomComparisonHom_transport σ hi' hj' hAi hBj,
      coherentHomComparisonHom_cast_last]
    simp only [← Category.assoc]
    exact congrArg (fun f ↦ f ≫ SSet.yonedaEquiv.symm σ)
      (coherentPrismCut_maximumMap t i j hi hj)
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have hle := Path.le (P.obj 0)
    change i ≤ j at hle
    have h := t.monotone hle
    rw [hj] at h
    exact False.elim (hi (le_antisymm h (Fin.zero_le _)))
  · let hAi := coherentHomComparisonObj_last X Y n
    let hBj := coherentHomComparisonObj_last X Y n
    let hi' := coherentPrismCut_one t i hi
    let hj' := coherentPrismCut_one t j hj
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      ((congrArg (coherentHomComparisonObj X Y) hi').trans hAi)
      ((congrArg (coherentHomComparisonObj X Y) hj').trans hBj)))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [coherentCompositionHom_one_one σ τ t i j hi hj,
      coherentHomComparisonHom_transport σ hi' hj' hAi hBj,
      coherentHomComparisonHom_last_last]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    rfl

end SerrePositivity.InfinityCategories
