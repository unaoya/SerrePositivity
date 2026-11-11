module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.UnitComposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HornData

/-!
概要：二単体の真部分区間を保って、全区間 Hom だけを指定写像へ置き換える。
方針：唯一の内部合成条件から豊穣関手則を回収し、端点での合成は単位則を使う。
規約：写像の存在と合成条件は呼出し側で実構成する。
使われ方：Ind-S (9) の座標畳み込みによる制御二単体。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {C : Type v} [Category.{u} C] [SimplicialCategory C]
variable (t : (SimplicialNerve C) _⦋2⦌)
variable (g : nerve (Path (ULift.up (0 : Fin 3) : ULift.{u} (Fin 3)) (ULift.up 2)) ⟶
  SimplicialCategory.sHom (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up 2⟩))

/-- 全区間のみを置き換えた Hom のデータ。 -/
def triangleReplacedHom (i j : Fin 3) :
    nerve (Path (ULift.up i : ULift.{u} (Fin 3)) (ULift.up j)) ⟶
      SimplicialCategory.sHom (t.obj ⟨ULift.up i⟩) (t.obj ⟨ULift.up j⟩) := by
  by_cases hi : i = 0
  · by_cases hj : j = 2
    · subst i j
      exact g
    · exact t.map ⟨ULift.up i⟩ ⟨ULift.up j⟩
  · exact t.map ⟨ULift.up i⟩ ⟨ULift.up j⟩

/-- 真部分区間では元の Hom に厳密に一致する。 -/
lemma triangleReplacedHom_proper (i j : Fin 3) (h : i ≠ 0 ∨ j ≠ 2) :
    triangleReplacedHom t g i j = t.map ⟨ULift.up i⟩ ⟨ULift.up j⟩ := by
  rcases h with h | h
  · simp only [triangleReplacedHom, dite_eq_right h]
  · by_cases hi : i = 0
    · simp only [triangleReplacedHom, dite_eq_left hi, dite_eq_right h]
    · simp only [triangleReplacedHom, dite_eq_right hi]

/-- 全区間では与えられた Hom そのもの。 -/
lemma triangleReplacedHom_full : triangleReplacedHom t g 0 2 = g := by
  simp [triangleReplacedHom]

/-- 単位は全区間の変更に影響されない。 -/
lemma triangleReplacedHom_id (i : Fin 3) :
    eId SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin 3))) ≫
      triangleReplacedHom t g i i = eId SSet (t.obj ⟨ULift.up i⟩) := by
  rw [triangleReplacedHom_proper t g i i (by omega)]
  exact t.map_id _

/-- 内部切断点での合成を保つ全区間 Hom は、元の真部分区間と豊穣関手を作る。 -/
def triangleReplaceLongHom
    (hg : ∀ j : Fin 3, 0 < j → j < 2 →
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 3)) (ULift.up j) (ULift.up 2) ≫ g =
        (t.map ⟨ULift.up 0⟩ ⟨ULift.up j⟩ ⊗ₘ t.map ⟨ULift.up j⟩ ⟨ULift.up 2⟩) ≫
          eComp SSet (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up j⟩) (t.obj ⟨ULift.up 2⟩)) :
    (SimplicialNerve C) _⦋2⦌ where
  obj := t.obj
  map i j := triangleReplacedHom t g i.as.down j.as.down
  map_id i := triangleReplacedHom_id t g i.as.down
  map_comp := by
    rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨k⟩⟩
    change Fin 3 at i j k
    by_cases hij : i ≤ j
    swap
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathProduct_empty_hom_ext (ULift.up i) (ULift.up j) (ULift.up k)
        (Or.inl hij) _ _
    by_cases hjk : j ≤ k
    swap
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathProduct_empty_hom_ext (ULift.up i) (ULift.up j) (ULift.up k)
        (Or.inr hjk) _ _
    by_cases h : i ≠ 0 ∨ k ≠ 2
    · rw [triangleReplacedHom_proper t g i k h,
        triangleReplacedHom_proper t g i j (by omega),
        triangleReplacedHom_proper t g j k (by omega)]
      exact t.map_comp _ _ _
    have hi : i = 0 := by tauto
    have hk : k = 2 := by tauto
    subst i k
    rw [triangleReplacedHom_full]
    by_cases hj : j = 0
    · subst j
      rw [triangleReplacedHom_full]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHom_comp_left_unit _ _ _ _ _ _ (triangleReplacedHom_id t g 0)
    by_cases hj' : j = 2
    · subst j
      rw [triangleReplacedHom_full]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHom_comp_right_unit _ _ _ _ _ _ (triangleReplacedHom_id t g 2)
    rw [triangleReplacedHom_proper t g 0 j (Or.inr hj'),
      triangleReplacedHom_proper t g j 2 (Or.inl hj)]
    exact hg j (by omega) (by omega)


variable (hg : ∀ j : Fin 3, 0 < j → j < 2 →
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 3)) (ULift.up j) (ULift.up 2) ≫ g =
    (t.map ⟨ULift.up 0⟩ ⟨ULift.up j⟩ ⊗ₘ t.map ⟨ULift.up j⟩ ⟨ULift.up 2⟩) ≫
      eComp SSet (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up j⟩) (t.obj ⟨ULift.up 2⟩))

/-- 全区間 Hom の置換は零番面を変えない。 -/
lemma triangleReplaceLongHom_face_zero :
    (SimplicialNerve C).δ (0 : Fin 3) (triangleReplaceLongHom t g hg) =
      (SimplicialNerve C).δ (0 : Fin 3) t := by
  change (SimplicialThickening.functor (SimplexCategory.δ (0 : Fin 3)).toOrderHom.uliftMap).comp
    SSet (triangleReplaceLongHom t g hg) =
    (SimplicialThickening.functor (SimplexCategory.δ (0 : Fin 3)).toOrderHom.uliftMap).comp SSet t
  refine EnrichedFunctor.ext SSet
    (F := (SimplicialThickening.functor (SimplexCategory.δ (0 : Fin 3)).toOrderHom.uliftMap).comp
      SSet (triangleReplaceLongHom t g hg))
    (G := (SimplicialThickening.functor (SimplexCategory.δ (0 : Fin 3)).toOrderHom.uliftMap).comp
      SSet t) (fun _ => rfl) ?_
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  simp only [eqToHom_refl, Category.comp_id]
  change _ ≫ triangleReplacedHom t g ((0 : Fin 3).succAbove i)
      ((0 : Fin 3).succAbove j) = _
  rw [triangleReplacedHom_proper t g _ _ (Or.inl (Fin.succAbove_ne 0 i))]
  rfl

/-- 全区間 Hom の置換は二番面を変えない。 -/
lemma triangleReplaceLongHom_face_two :
    (SimplicialNerve C).δ (2 : Fin 3) (triangleReplaceLongHom t g hg) =
      (SimplicialNerve C).δ (2 : Fin 3) t := by
  change (SimplicialThickening.functor (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap).comp
    SSet (triangleReplaceLongHom t g hg) =
    (SimplicialThickening.functor (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap).comp SSet t
  refine EnrichedFunctor.ext SSet
    (F := (SimplicialThickening.functor (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap).comp
      SSet (triangleReplaceLongHom t g hg))
    (G := (SimplicialThickening.functor (SimplexCategory.δ (2 : Fin 3)).toOrderHom.uliftMap).comp
      SSet t) (fun _ => rfl) ?_
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  simp only [eqToHom_refl, Category.comp_id]
  change _ ≫ triangleReplacedHom t g ((2 : Fin 3).succAbove i)
      ((2 : Fin 3).succAbove j) = _
  rw [triangleReplacedHom_proper t g _ _ (Or.inr (Fin.succAbove_ne 2 j))]
  rfl

/-- 置換した二単体は、指定された全 native Hom を厳密に回収する。 -/
lemma triangleReplaceLongHom_map :
    (triangleReplaceLongHom t g hg).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ = g :=
  triangleReplacedHom_full t g

/-- 同じ全長 Hom の置換は元の二単体を変えない。 -/
lemma triangleReplaceLongHom_self :
    triangleReplaceLongHom t (t.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
      (fun j _ _ => t.map_comp ⟨ULift.up 0⟩ ⟨ULift.up j⟩ ⟨ULift.up 2⟩) = t := by
  refine EnrichedFunctor.ext SSet (F := triangleReplaceLongHom t _ _)
    (G := t) (fun _ => rfl) ?_
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change Fin 3 at i j
  simp only [eqToHom_refl, Category.comp_id]
  change triangleReplacedHom t _ i j = _
  by_cases h : i ≠ 0 ∨ j ≠ 2
  · exact triangleReplacedHom_proper t _ i j h
  · have hi : i = 0 := by tauto
    have hj : j = 2 := by tauto
    subst i j
    exact triangleReplacedHom_full t _

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
