module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.SimplicialSum
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Pullbacks

/-!
# 添字付き余積の引き戻し

概要：余積の射の自然性の四角形と、添字を写す成分ごとの四角形を引き戻しとして扱う。
方針：各次数で依存和の添字を等式から復元し、成分の引き戻しの存在と一意性を使う。
規約：Segal 1974 Lemma 1.8。添字の写像の単射性は仮定しない。
使われ方：telescope の偶数・奇数への二射の四角形。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.Comparison
end SerrePositivity.KST.Comparison
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.Comparison
open CategoryTheory Limits
variable {ι κ : Type v}

/--
概要：添字を指定した写像で移す余積の射。
方針：各成分の射の後で指定された終域の包含を合成する。
規約：添字の写像は単射でなくてもよい。
使われ方：telescope の辺から偶数・奇数の頂点への射。
-/
def simplicialSumReindex {A : ι → SSet.{max u v}} {B : κ → SSet.{max u v}}
    (σ : ι → κ) (f : ∀ i, A i ⟶ B (σ i)) : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum A ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum B :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumDesc (fun i => f i ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion B (σ i))

/--
概要：添字を写す余積の射の成分への制限。
方針：依存和からの desc の定義を計算する。
規約：指定した添字の像の成分へ入る。
使われ方：余積の四角形の可換性。
-/
@[simp] theorem simplicialSumInclusion_reindex {A : ι → SSet.{max u v}}
    {B : κ → SSet.{max u v}} (σ : ι → κ) (f : ∀ i, A i ⟶ B (σ i)) (i : ι) :
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion A i ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex σ f =
      f i ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion B (σ i) := rfl

/--
概要：成分ごとの可換な四角形から余積の可換な四角形を得る。
方針：各成分への制限の式を計算する。
規約：添字の写像は任意。
使われ方：余積のホモトピー引き戻しの四角形。
-/
theorem simplicialSumReindex_commSq {A C : ι → SSet.{max u v}}
    {B D : κ → SSet.{max u v}} (σ : ι → κ)
    (a : ∀ i, A i ⟶ B (σ i)) (w : ∀ i, A i ⟶ C i)
    (v : ∀ j, B j ⟶ D j) (c : ∀ i, C i ⟶ D (σ i))
    (h : ∀ i, CommSq (a i) (w i) (v (σ i)) (c i)) :
    CommSq (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex σ a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap w)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap v) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex σ c) := by
  constructor
  apply _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSum_hom_ext
  intro i
  simp only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_reindex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_map]
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_reindex, _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_map]
  rw [← Category.assoc, (h i).w, Category.assoc]

/--
概要：添字を写す成分ごとの引き戻しは、余積の四角形も引き戻しにする。
方針：下左の添字を固定し、上右の添字がその像であることを等式から読み取る。
規約：厳密な引き戻しであり、ホモトピー引き戻しへの移行は別途行う。
使われ方：telescope の二面の厳密な場合。
-/
theorem simplicialSumReindex_isPullback {A C : ι → SSet.{max u v}}
    {B D : κ → SSet.{max u v}} (σ : ι → κ)
    (a : ∀ i, A i ⟶ B (σ i)) (w : ∀ i, A i ⟶ C i)
    (v : ∀ j, B j ⟶ D j) (c : ∀ i, C i ⟶ D (σ i))
    (h : ∀ i, IsPullback (a i) (w i) (v (σ i)) (c i)) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex σ a) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap w)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap v) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex σ c) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  let ev := (evaluation SimplexCategoryᵒᵖ (Type (max u v))).obj d
  have h' i := (h i).map ev
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (Sigma.mk (σ x.1)) (congrArg (fun t => t.app d x.2) (h x.1).w)
  · rintro ⟨i, x⟩ ⟨j, y⟩ ⟨h₁, h₂⟩
    change (⟨i, (w i).app d x⟩ : Σ k, (C k).obj d) = ⟨j, (w j).app d y⟩ at h₂
    have hij : i = j := congrArg Sigma.fst h₂
    subst j
    have he : (⟨σ i, (a i).app d x⟩ : Σ k, (B k).obj d) =
        ⟨σ i, (a i).app d y⟩ := h₁
    have ha : (a i).app d x = (a i).app d y := eq_of_heq (Sigma.mk.inj he).2
    have hw : (w i).app d x = (w i).app d y := by simpa using h₂
    exact congrArg (Sigma.mk i) (Types.ext_of_isPullback (h' i) ha hw)
  · rintro ⟨j, b⟩ ⟨i, z⟩ he
    change (⟨j, (v j).app d b⟩ : Σ k, (D k).obj d) = ⟨σ i, (c i).app d z⟩ at he
    have hj : j = σ i := congrArg Sigma.fst he
    subst j
    have hv : (v (σ i)).app d b = (c i).app d z := by simpa using he
    obtain ⟨x, hx, hz⟩ := Types.exists_of_isPullback (h' i) b z hv
    exact ⟨⟨i, x⟩, congrArg (Sigma.mk (σ i)) hx, congrArg (Sigma.mk i) hz⟩

/--
概要：余積への各成分の包含の自然性の四角形は引き戻しである。
方針：依存和の添字と値を各次数で分けて確認する。
規約：成分の射には条件を課さない。
使われ方：余積の Kan 条件と各段階のファイバー。
-/
theorem simplicialSumInclusion_isPullback {A B : ι → SSet.{max u v}}
    (f : ∀ i, A i ⟶ B i) (i : ι) :
    IsPullback (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion A i) (f i)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumMap f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion B i) := by
  apply IsPullback.of_forall_isPullback_app
  intro d
  apply (Types.isPullback_iff _ _ _ _).mpr
  refine ⟨rfl, ?_, ?_⟩
  · intro x y h
    have he : (⟨i, x⟩ : Σ k, (A k).obj d) = ⟨i, y⟩ := h.1
    simpa using he
  · rintro ⟨j, x⟩ y h
    change (⟨j, (f j).app d x⟩ : Σ k, (B k).obj d) = ⟨i, y⟩ at h
    have hj : j = i := congrArg Sigma.fst h
    subst j
    refine ⟨x, rfl, ?_⟩
    simpa using h

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumInclusion_isPullback := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_isPullback

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumInclusion_reindex := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumInclusion_reindex

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumReindex := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumReindex_commSq := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex_commSq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Comparison.simplicialSumReindex_isPullback := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplicialSumReindex_isPullback
