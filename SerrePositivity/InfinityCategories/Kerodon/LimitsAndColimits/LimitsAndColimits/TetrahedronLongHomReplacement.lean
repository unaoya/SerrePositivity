module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.UnitComposition
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HornData

/-!
概要：三単体の真部分区間を保って、全区間 Hom だけを指定写像へ置き換える。
方針：二つの内部合成条件から豊穣関手則を回収し、端点での合成は単位則を使う。
規約：写像の存在と二つの合成条件は呼出し側で実構成する。
使われ方：Ind-S (9b) の座標畳み込みによる制御三単体。

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
variable (t : (SimplicialNerve C) _⦋3⦌)
variable (g : nerve (Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3)) ⟶
  SimplicialCategory.sHom (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up 3⟩))

/-- 全区間のみを置き換えた Hom のデータ。 -/
def tetrahedronReplacedHom (i j : Fin 4) :
    nerve (Path (ULift.up i : ULift.{u} (Fin 4)) (ULift.up j)) ⟶
      SimplicialCategory.sHom (t.obj ⟨ULift.up i⟩) (t.obj ⟨ULift.up j⟩) := by
  by_cases hi : i = 0
  · by_cases hj : j = 3
    · subst i j
      exact g
    · exact t.map ⟨ULift.up i⟩ ⟨ULift.up j⟩
  · exact t.map ⟨ULift.up i⟩ ⟨ULift.up j⟩

/-- 真部分区間では元の Hom に厳密に一致する。 -/
lemma tetrahedronReplacedHom_proper (i j : Fin 4) (h : i ≠ 0 ∨ j ≠ 3) :
    tetrahedronReplacedHom t g i j = t.map ⟨ULift.up i⟩ ⟨ULift.up j⟩ := by
  rcases h with h | h
  · simp only [tetrahedronReplacedHom, dite_eq_right h]
  · by_cases hi : i = 0
    · simp only [tetrahedronReplacedHom, dite_eq_left hi, dite_eq_right h]
    · simp only [tetrahedronReplacedHom, dite_eq_right hi]

/-- 全区間では与えられた Hom そのもの。 -/
lemma tetrahedronReplacedHom_full : tetrahedronReplacedHom t g 0 3 = g := by
  simp [tetrahedronReplacedHom]

/-- 単位は全区間の変更に影響されない。 -/
lemma tetrahedronReplacedHom_id (i : Fin 4) :
    eId SSet (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin 4))) ≫
      tetrahedronReplacedHom t g i i = eId SSet (t.obj ⟨ULift.up i⟩) := by
  rw [tetrahedronReplacedHom_proper t g i i (by omega)]
  exact t.map_id _

/-- 内部二切断点での合成を保つ全区間 Hom は、元の真部分区間と豊穣関手を作る。 -/
def tetrahedronReplaceLongHom
    (hg : ∀ j : Fin 4, 0 < j → j < 3 →
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 4)) (ULift.up j) (ULift.up 3) ≫ g =
        (t.map ⟨ULift.up 0⟩ ⟨ULift.up j⟩ ⊗ₘ t.map ⟨ULift.up j⟩ ⟨ULift.up 3⟩) ≫
          eComp SSet (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up j⟩) (t.obj ⟨ULift.up 3⟩)) :
    (SimplicialNerve C) _⦋3⦌ where
  obj := t.obj
  map i j := tetrahedronReplacedHom t g i.as.down j.as.down
  map_id i := tetrahedronReplacedHom_id t g i.as.down
  map_comp := by
    rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨k⟩⟩
    change Fin 4 at i j k
    by_cases hij : i ≤ j
    swap
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathProduct_empty_hom_ext (ULift.up i) (ULift.up j) (ULift.up k)
        (Or.inl hij) _ _
    by_cases hjk : j ≤ k
    swap
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathProduct_empty_hom_ext (ULift.up i) (ULift.up j) (ULift.up k)
        (Or.inr hjk) _ _
    by_cases h : i ≠ 0 ∨ k ≠ 3
    · rw [tetrahedronReplacedHom_proper t g i k h,
        tetrahedronReplacedHom_proper t g i j (by omega),
        tetrahedronReplacedHom_proper t g j k (by omega)]
      exact t.map_comp _ _ _
    have hi : i = 0 := by tauto
    have hk : k = 3 := by tauto
    subst i k
    rw [tetrahedronReplacedHom_full]
    by_cases hj : j = 0
    · subst j
      rw [tetrahedronReplacedHom_full]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHom_comp_left_unit _ _ _ _ _ _ (tetrahedronReplacedHom_id t g 0)
    by_cases hj' : j = 3
    · subst j
      rw [tetrahedronReplacedHom_full]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathHom_comp_right_unit _ _ _ _ _ _ (tetrahedronReplacedHom_id t g 3)
    rw [tetrahedronReplacedHom_proper t g 0 j (Or.inr hj'),
      tetrahedronReplacedHom_proper t g j 3 (Or.inl hj)]
    exact hg j (by omega) (by omega)


variable (hg : ∀ j : Fin 4, 0 < j → j < 3 →
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 4)) (ULift.up j) (ULift.up 3) ≫ g =
    (t.map ⟨ULift.up 0⟩ ⟨ULift.up j⟩ ⊗ₘ t.map ⟨ULift.up j⟩ ⟨ULift.up 3⟩) ≫
      eComp SSet (t.obj ⟨ULift.up 0⟩) (t.obj ⟨ULift.up j⟩) (t.obj ⟨ULift.up 3⟩))

/-- 全区間 Hom の置換は零番面を変えない。 -/
lemma tetrahedronReplaceLongHom_face_zero :
    (SimplicialNerve C).δ (0 : Fin 4) (tetrahedronReplaceLongHom t g hg) =
      (SimplicialNerve C).δ (0 : Fin 4) t := by
  change (SimplicialThickening.functor (SimplexCategory.δ (0 : Fin 4)).toOrderHom.uliftMap).comp
    SSet (tetrahedronReplaceLongHom t g hg) =
    (SimplicialThickening.functor (SimplexCategory.δ (0 : Fin 4)).toOrderHom.uliftMap).comp SSet t
  refine EnrichedFunctor.ext SSet
    (F := (SimplicialThickening.functor (SimplexCategory.δ (0 : Fin 4)).toOrderHom.uliftMap).comp
      SSet (tetrahedronReplaceLongHom t g hg))
    (G := (SimplicialThickening.functor (SimplexCategory.δ (0 : Fin 4)).toOrderHom.uliftMap).comp
      SSet t) (fun _ => rfl) ?_
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  simp only [eqToHom_refl, Category.comp_id]
  change _ ≫ tetrahedronReplacedHom t g ((0 : Fin 4).succAbove i)
      ((0 : Fin 4).succAbove j) = _
  rw [tetrahedronReplacedHom_proper t g _ _ (Or.inl (Fin.succAbove_ne 0 i))]
  rfl

/-- 全区間 Hom の置換は三番面を変えない。 -/
lemma tetrahedronReplaceLongHom_face_three :
    (SimplicialNerve C).δ (3 : Fin 4) (tetrahedronReplaceLongHom t g hg) =
      (SimplicialNerve C).δ (3 : Fin 4) t := by
  change (SimplicialThickening.functor (SimplexCategory.δ (3 : Fin 4)).toOrderHom.uliftMap).comp
    SSet (tetrahedronReplaceLongHom t g hg) =
    (SimplicialThickening.functor (SimplexCategory.δ (3 : Fin 4)).toOrderHom.uliftMap).comp SSet t
  refine EnrichedFunctor.ext SSet
    (F := (SimplicialThickening.functor (SimplexCategory.δ (3 : Fin 4)).toOrderHom.uliftMap).comp
      SSet (tetrahedronReplaceLongHom t g hg))
    (G := (SimplicialThickening.functor (SimplexCategory.δ (3 : Fin 4)).toOrderHom.uliftMap).comp
      SSet t) (fun _ => rfl) ?_
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  simp only [eqToHom_refl, Category.comp_id]
  change _ ≫ tetrahedronReplacedHom t g ((3 : Fin 4).succAbove i)
      ((3 : Fin 4).succAbove j) = _
  rw [tetrahedronReplacedHom_proper t g _ _ (Or.inr (Fin.succAbove_ne 3 j))]
  rfl

/-- 一番面の全 Hom への制限を保持する置換は、その面全体を保持する。 -/
lemma tetrahedronReplaceLongHom_face_one
    (hface : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap (1 : Fin 4) 0 2 ≫ g =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap (1 : Fin 4) 0 2 ≫ t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩) :
    (SimplicialNerve C).δ (1 : Fin 4) (tetrahedronReplaceLongHom t g hg) =
      (SimplicialNerve C).δ (1 : Fin 4) t := by
  refine EnrichedFunctor.ext SSet
    (F := (SimplicialThickening.functor (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap).comp
      SSet (tetrahedronReplaceLongHom t g hg))
    (G := (SimplicialThickening.functor (SimplexCategory.δ (1 : Fin 4)).toOrderHom.uliftMap).comp
      SSet t) (fun _ => rfl) ?_
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change Fin 3 at i j
  simp only [eqToHom_refl, Category.comp_id]
  change _ ≫ tetrahedronReplacedHom t g ((1 : Fin 4).succAbove i)
      ((1 : Fin 4).succAbove j) = _
  by_cases hij : i = 0 ∧ j = 2
  · rcases hij with ⟨rfl, rfl⟩
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathFaceMap (1 : Fin 4) 0 2 ≫ tetrahedronReplacedHom t g 0 3 = _
    rw [tetrahedronReplacedHom_full]
    exact hface
  · rw [tetrahedronReplacedHom_proper t g _ _ (by
      fin_cases i <;> fin_cases j <;> first | decide | simp_all)]
    rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
