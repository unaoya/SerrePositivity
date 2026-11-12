module
public import SerrePositivity.KST.SConstruction.DegeneratePushouts
public import SerrePositivity.KST.SConstruction.Gapped

/-! # 退化する区間正方形
概要：一対の端点が等しい区間正方形は恒等辺を持ち、任意の図式で押し出しとなる。
方針：左右の端点の選択を計算し、正方形が一方の座標だけに依存することを示す。
規約：HTT Lemma 4.4.2.1 と BGT Definition 7.1 の退化した場合。
使われ方：S_1 の gapped 条件と第一行制限の低次数。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：左の二端点が等しい区間正方形は下辺を垂直に定値延長したもの。
方針：縦座標の端点選択が常に同じ値となる。
規約：全次数で厳密な形状の等号。使われ方：恒等垂直辺の押し出し。 -/
lemma arSquare_repeat_left {n : ℕ} (i k l : Fin (n + 1)) (hik : i ≤ k) (hkl : k ≤ l) :
    arSquare i i k l le_rfl hik hkl = CartesianMonoidalCategory.fst _ _ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ arSquare i i k l le_rfl hik hkl := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · change (if _ = 0 then i else i) = _
    simp only [ite_self]
    rfl
  · rfl

/-- 概要：右の二端点が等しい区間正方形は左辺を水平に定値延長したもの。
方針：横座標の端点選択が常に同じ値となる。
規約：全次数で厳密な形状の等号。使われ方：恒等水平辺の押し出し。 -/
lemma arSquare_repeat_right {n : ℕ} (i j k : Fin (n + 1)) (hij : i ≤ j) (hjk : j ≤ k) :
    arSquare i j k k hij hjk le_rfl = CartesianMonoidalCategory.snd _ _ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ arSquare i j k k hij hjk le_rfl := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.ext (fun r => ?_) (fun _ _ _ => Subsingleton.elim _ _)
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change (if _ = 0 then k else k) = _
    simp only [ite_self]
    rfl

/-- 概要：退化した区間正方形は任意の quasicategory の図式で押し出し。
方針：端点の一致により一方の座標にだけ依存し、恒等辺の押し出し性を適用する。
規約：零対象・安定性は不要。使われ方：低次数の gapped 条件。 -/
lemma arSquare_isPushout_of_repeated_endpoints {n : ℕ} {C : SSet.{u}} [Quasicategory C]
    (F : arNerve n ⟶ C) (i j k l : Fin (n + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hkl : k ≤ l) (h : i = j ∨ k = l) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (arSquare i j k l hij hjk hkl ≫ F) := by
  rcases h with h | h
  · subst j
    have he := congrArg (fun f => f ≫ F) (arSquare_repeat_left i k l hjk hkl)
    simp only [Category.assoc] at he
    rw [he]
    exact isPushoutSquare_fst _
  · subst l
    have he := congrArg (fun f => f ≫ F) (arSquare_repeat_right i j k hij hjk)
    simp only [Category.assoc] at he
    rw [he]
    exact isPushoutSquare_snd _

/-- 概要：Ar[1] の図式は、対角が零なら gapped。
方針：Fin 2 の四つの弱増加端点では左右どちらかの組が等しい。
規約：C は quasicategory。使われ方：S_1 の第一行制限の零次元の存在。 -/
lemma isGapped_one_of_zero_diagonal {C : SSet.{u}} [Quasicategory C]
    (F : arNerve 1 ⟶ C)
    (hz : ∀ j : Fin 2, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (F.app (Opposite.op ⦋0⦌)
      (ComposableArrows.mk₀ (arObj j j le_rfl)))) : IsGapped F := by
  refine ⟨hz, ?_⟩
  intro i j k l hij hjk hkl
  apply arSquare_isPushout_of_repeated_endpoints F i j k l hij hjk hkl
  by_cases h : i = j
  · exact Or.inl h
  · right
    have hne : i.val ≠ j.val := fun he => h (Fin.ext he)
    apply Fin.ext
    have hi := i.isLt
    have hj := j.isLt
    have hk := k.isLt
    have hl := l.isLt
    change i.val ≤ j.val at hij
    change j.val ≤ k.val at hjk
    change k.val ≤ l.val at hkl
    omega

end SerrePositivity.KST.SConstruction
