module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutStage
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionCoordinates

/-!
概要：同じ edgewise Hom 単体から、左右を補間する coherent な二対象の単体を作る。
方針：対象の二値ラベルと補間段階を分け、交差する Hom を混合座標で評価する。
規約：Hom や coherent nerve の Kan 性を要求しない。
使われ方：反転 Hom の左右の区間比較を全パラメーターで結ぶ。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 二値ラベルに従って元の二対象を配置する。 -/
def coherentTwoSidedHomObj {C : Type v} (X Y : C) {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) : C := if t i = 0 then X else Y

/-- 一側から零側へ戻る path は存在しない。 -/
lemma pathCutSameSimplex_backward_false {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i ≠ 0) (hj : t j = 0)
    (P : Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) : False := by
  have hp := Path.le P
  change i ≤ j at hp
  have h := t.monotone hp
  rw [hj] at h
  exact hi (le_antisymm h (Fin.zero_le _))

/-- 逆向きの空の Hom を任意の標的へ写す。 -/
def coherentTwoSidedBackwardMap {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i ≠ 0) (hj : t j = 0) (A : SSet.{u}) :
    nerve (Path (ULift.up i : ULift.{u} (Fin (n + 1))) (ULift.up j)) ⟶ A where
  app _ := ↾fun P => False.elim (pathCutSameSimplex_backward_false t hi hj (P.obj 0))
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro P
    exact False.elim (pathCutSameSimplex_backward_false t hi hj (P.obj 0))

/-- 同じ二対象の間は恒等、交差部分では共通 Hom の混合座標を評価する。 -/
def coherentTwoSidedHom {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) :
    SimplicialCategory.sHom
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ⟨ULift.up j⟩ ⟶
    SimplicialCategory.sHom (coherentTwoSidedHomObj X Y t i)
      (coherentTwoSidedHomObj X Y t j) := by
  by_cases hi : t i = 0 <;> by_cases hj : t j = 0
  · simp only [coherentTwoSidedHomObj, hi, hj, ite_true]
    exact toUnit _ ≫ eId SSet X
  · simp only [coherentTwoSidedHomObj, hi, hj, ite_true, ite_false]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap t s hi (by omega) σ
  · simp only [coherentTwoSidedHomObj, hi, hj, ite_true, ite_false]
    exact coherentTwoSidedBackwardMap t hi hj _
  · simp only [coherentTwoSidedHomObj, hi, hj, ite_false]
    exact toUnit _ ≫ eId SSet Y

/-- 混合 Hom の作用は豊穣恒等を保つ。 -/
lemma coherentTwoSidedHom_map_id {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) :
    eId SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1)))) ≫
      coherentTwoSidedHom σ t s i i = eId SSet (coherentTwoSidedHomObj X Y t i) := by
  by_cases hi : t i = 0
  all_goals
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro a
    simp -implicitDefEqProofs +instances [coherentTwoSidedHom, coherentTwoSidedHomObj, hi]

/-- 零ラベルの対象を元の始域へ正規化する。 -/
lemma coherentTwoSidedHomObj_zero {C : Type v} (X Y : C) {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i = 0) :
    coherentTwoSidedHomObj X Y t i = X := by simp only [coherentTwoSidedHomObj, hi, ite_true]

/-- 一ラベルの対象を元の標的へ正規化する。 -/
lemma coherentTwoSidedHomObj_one {C : Type v} (X Y : C) {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i ≠ 0) :
    coherentTwoSidedHomObj X Y t i = Y := by simp only [coherentTwoSidedHomObj, hi, ite_false]

/-- 正規化した zero_zero の Hom は定義した同じ作用を回収する。 -/
lemma coherentTwoSidedHom_zero_zero {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 0) :
    coherentTwoSidedHom σ t s i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentTwoSidedHomObj_zero X Y t i hi)
      (coherentTwoSidedHomObj_zero X Y t j hj)) = toUnit _ ≫ eId SSet X := by
  simp -implicitDefEqProofs +instances [coherentTwoSidedHom, coherentTwoSidedHomObj_zero,
    coherentTwoSidedHomObj_zero, hi, hj, Category.assoc]

/-- 正規化した zero_one の Hom は定義した同じ作用を回収する。 -/
lemma coherentTwoSidedHom_zero_one {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j ≠ 0) :
    coherentTwoSidedHom σ t s i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentTwoSidedHomObj_zero X Y t i hi)
      (coherentTwoSidedHomObj_one X Y t j hj)) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap t s hi (by omega) σ := by
  simp -implicitDefEqProofs +instances [coherentTwoSidedHom, coherentTwoSidedHomObj_zero,
    coherentTwoSidedHomObj_one, hi, hj, Category.assoc]

/-- 正規化した one_one の Hom は定義した同じ作用を回収する。 -/
lemma coherentTwoSidedHom_one_one {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) (i j : Fin (n + 1)) (hi : t i ≠ 0) (hj : t j ≠ 0) :
    coherentTwoSidedHom σ t s i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentTwoSidedHomObj_one X Y t i hi)
      (coherentTwoSidedHomObj_one X Y t j hj)) = toUnit _ ≫ eId SSet Y := by
  simp -implicitDefEqProofs +instances [coherentTwoSidedHom, coherentTwoSidedHomObj_one,
    coherentTwoSidedHomObj_one, hi, hj, Category.assoc]

/-- 混合 Hom の作用は、全ての補間段階で豊穣合成を保つ。 -/
lemma coherentTwoSidedHom_map_comp {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) (i j k : Fin (n + 1)) :
    eComp SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))
        ⟨ULift.up j⟩ ⟨ULift.up k⟩ ≫ coherentTwoSidedHom σ t s i k =
      (coherentTwoSidedHom σ t s i j ⊗ₘ coherentTwoSidedHom σ t s j k) ≫
        eComp SSet (coherentTwoSidedHomObj X Y t i) (coherentTwoSidedHomObj X Y t j)
          (coherentTwoSidedHomObj X Y t k) := by
  let hX := fun i hi => coherentTwoSidedHomObj_zero X Y t i hi
  let hY := fun i hi => coherentTwoSidedHomObj_one X Y t i hi
  by_cases hi : t i = 0 <;> by_cases hj : t j = 0 <;> by_cases hk : t k = 0
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized (hX i hi) (hX j hj) (hX k hk) _ _ _ _).2
    simp only [coherentTwoSidedHom_zero_zero σ t s i k hi hk,
      coherentTwoSidedHom_zero_zero σ t s i j hi hj,
      coherentTwoSidedHom_zero_zero σ t s j k hj hk]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app X X d _).symm
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized (hX i hi) (hX j hj) (hY k hk) _ _ _ _).2
    simp only [coherentTwoSidedHom_zero_one σ t s i k hi hk,
      coherentTwoSidedHom_zero_zero σ t s i j hi hj,
      coherentTwoSidedHom_zero_one σ t s j k hj hk]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap_comp_zero t s hi hj (show t k = 1 by omega)]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app X Y d _).symm
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    exact False.elim (pathCutSameSimplex_backward_false t hj hk (Q.obj 0))
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized (hX i hi) (hY j hj) (hY k hk) _ _ _ _).2
    simp only [coherentTwoSidedHom_zero_one σ t s i k hi hk,
      coherentTwoSidedHom_zero_one σ t s i j hi hj,
      coherentTwoSidedHom_one_one σ t s j k hj hk]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutEdgewiseStageMap_comp_one t s hi (show t j = 1 by omega)
      (show t k = 1 by omega)]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_comp_id_app X Y d _).symm
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    exact False.elim (pathCutSameSimplex_backward_false t hi hj (P.obj 0))
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    exact False.elim (pathCutSameSimplex_backward_false t hi hj (P.obj 0))
  · apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    exact False.elim (pathCutSameSimplex_backward_false t hj hk (Q.obj 0))
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized (hY i hi) (hY j hj) (hY k hk) _ _ _ _).2
    simp only [coherentTwoSidedHom_one_one σ t s i k hi hk,
      coherentTwoSidedHom_one_one σ t s i j hi hj,
      coherentTwoSidedHom_one_one σ t s j k hj hk]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app Y Y d _).symm

/-- 全 Hom の共通解像の単体を、左右を補間する実際の coherent 単体へ写す。 -/
def coherentTwoSidedHomSimplex {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision (SimplicialCategory.sHom X Y)) _⦋n⦌)
    (t s : Fin (n + 1) →o Fin 2) : (SimplicialNerve C) _⦋n⦌ where
  obj i := coherentTwoSidedHomObj X Y t i.as.down
  map i j := coherentTwoSidedHom σ t s i.as.down j.as.down
  map_id := by
    rintro ⟨⟨i⟩⟩
    exact coherentTwoSidedHom_map_id σ t s i
  map_comp := by
    rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨k⟩⟩
    exact coherentTwoSidedHom_map_comp σ t s i j k

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
