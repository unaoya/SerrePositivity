module

public import SerrePositivity.InfinityCategories.F1.Universe.InnerAnodyne
public import SerrePositivity.InfinityCategories.F1.Universe.TrivialKanFibration
public import SerrePositivity.InfinityCategories.F1B.CofinalAnodyneRecognition
public import SerrePositivity.InfinityCategories.F1B.TrivialFibrationCofinality

/-!
概要：小さい right cofinal map は宇宙を持ち上げても同じ写像として right cofinal。
方針：生成ホーンの移送で right anodyne 性を保ち、同じ因子分解の trivial Kan 後因子と合成する。
規約：大きい標的への cofinal 性を追加仮定にしない。
使われ方：小さい cofinal poset を宇宙 u+1 の前層図式へ適用する。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ右ホーンの宇宙持ち上げは、同じ番号の生成射と同型。 -/
lemma rightHornInclusions_ulift : rightHornInclusions.{u} ≤
    rightAnodyneExtensions.{max u v}.inverseImage (SSet.uliftFunctor.{v, u}) := by
  intro X Y f hf
  obtain @⟨n, i, h0⟩ := hf
  exact (rightAnodyneExtensions.arrow_mk_iso_iff
    (SimplicialModel.UniverseLift.hornArrowIso.{v, u} (n + 1) i)).mpr
      (rightAnodyneExtensions_horn i h0)

/-- 宇宙持ち上げは元の right anodyne 射を保つ。 -/
lemma rightAnodyneExtensions_ulift {A B : SSet.{u}} (f : A ⟶ B)
    (hf : rightAnodyneExtensions f) :
    rightAnodyneExtensions ((SSet.uliftFunctor.{v, u}).map f) := by
  have : rightHornInclusions.{u}.HasSmallObjectArgument.{u} := by
    rw [← cofinalRightHornFamily_eq]
    infer_instance
  exact ModelGeneration.generatedLeft_map (SSet.uliftFunctor.{v, u})
    rightAnodyneExtensions rightHornInclusions rightHornInclusions_ulift f hf

/-- 元の小さい right cofinal map を持ち上げた同じ写像も right cofinal。 -/
lemma isRightCofinal_ulift {A B : SSet.{u}} (f : A ⟶ B) (hf : IsRightCofinal f) :
    IsRightCofinal ((SSet.uliftFunctor.{v, u}).map f) := by
  obtain ⟨Z, j, p, hm, hj, hp, he⟩ := hf.exists_anodyne_trivialKan_factorization
  have : TrivialKanFibration p := hp
  have : TrivialKanFibration ((SSet.uliftFunctor.{v, u}).map p) :=
    trivialKanFibration_uliftFunctor_map p
  have h := (isRightCofinal_of_rightAnodyne _ (rightAnodyneExtensions_ulift j hj)).comp
    (isRightCofinal_of_trivialKanFibration ((SSet.uliftFunctor.{v, u}).map p))
  rw [← CategoryTheory.Functor.map_comp, he] at h
  exact h

end SerrePositivity.InfinityCategories.F2.Ind
