module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.PathCutMaps
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomComparison

/-!
概要：二つの豊穣 Hom の同時パラメーター付き合成の coherent な図式の対象と Hom。
方針：切替前を X、切替後を Y、追加した最後の頂点を Z に置く。
規約：合成に使う二つの Hom の単体は同じ次数を持つ。
使われ方：普遍 pointed-space 輸送と豊穣な一点 Hom の合成を結ぶ標準 prism。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：二段合成の図式の対象の作用。
方針：最後の頂点を Z、それ以外を二値ラベルで X または Y に分ける。
規約：X と Y が同じ対象でもよい。
使われ方：パラメーター付きの coherent な合成の対象データ。 -/
def coherentCompositionObj {C : Type v} (X Y Z : C) {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 2)) : C :=
  Fin.lastCases Z (fun i ↦ if t i = 0 then X else Y) i

/-- 概要：切替後から切替前へ戻る path は存在しない。
方針：path の端点の順序に二値ラベルの単調性を適用する。
規約：両端は追加した最後の頂点とは異なる。
使われ方：逆向きの豊穣 Hom の空性。 -/
lemma pathCut_backward_false {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i ≠ 0) (hj : t j = 0)
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2))) (ULift.up j.castSucc)) :
    False := by
  have h := Path.le P
  change i.castSucc ≤ j.castSucc at h
  have ht := t.monotone (Fin.castSucc_le_castSucc_iff.mp h)
  rw [hj] at ht
  exact hi (le_antisymm ht (Fin.zero_le _))

/-- 概要：切替後から切替前への空の Hom は任意の単体集合に写せる。
方針：各次数の旗の最初の path の不存在を使う。
規約：追加の初期対象の選択は不要。
使われ方：coherent な三対象の図式の逆向き Hom。 -/
def coherentCompositionBackwardMap {n : ℕ} (t : Fin (n + 1) →o Fin 2)
    {i j : Fin (n + 1)} (hi : t i ≠ 0) (hj : t j = 0) (A : SSet.{u}) :
    nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up j.castSucc)) ⟶ A where
  app _ := ↾fun P ↦ False.elim (pathCut_backward_false t hi hj (P.obj 0))
  naturality {a b} α := by
    apply ConcreteCategory.hom_ext
    intro P
    exact False.elim (pathCut_backward_false t hi hj (P.obj 0))

/-- 概要：二段合成の coherent な図式の Hom 上の作用。
方針：一段目は切替前の最大座標、二段目は最後の頂点以前の最大座標で評価する。
規約：X→Z ではこの二つの射を豊穣合成する。
使われ方：パラメーター付きの標準合成 prism の各単体の入力。 -/
noncomputable def coherentCompositionHom {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌)
    (t : Fin (n + 1) →o Fin 2) (i j : Fin (n + 2)) :
    SimplicialCategory.sHom
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ⟶
      SimplicialCategory.sHom (coherentCompositionObj X Y Z t i)
        (coherentCompositionObj X Y Z t j) := by
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last =>
      simp only [coherentCompositionObj, Fin.lastCases_last]
      exact toUnit _ ≫ eId SSet Z
    | cast j =>
      simp only [coherentCompositionObj, Fin.lastCases_last, Fin.lastCases_castSucc]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomEmptyMap j _
  | cast i =>
    induction j using Fin.lastCases with
    | last =>
      by_cases hi : t i = 0
      · simp only [coherentCompositionObj, Fin.lastCases_last, Fin.lastCases_castSucc, hi, ite_true]
        exact lift (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi (Fin.last (n + 1)) ≫ SSet.yonedaEquiv.symm σ)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm τ) ≫ eComp SSet X Y Z
      · simp only [coherentCompositionObj, Fin.lastCases_last, Fin.lastCases_castSucc,
          hi, ite_false]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm τ
    | cast j =>
      by_cases hi : t i = 0 <;> by_cases hj : t j = 0
      · simp only [coherentCompositionObj, Fin.lastCases_castSucc, hi, hj, ite_true]
        exact toUnit _ ≫ eId SSet X
      · simp only [coherentCompositionObj, Fin.lastCases_castSucc, hi, hj, ite_true, ite_false]
        exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi j.castSucc ≫ SSet.yonedaEquiv.symm σ
      · simp only [coherentCompositionObj, Fin.lastCases_castSucc, hi, hj, ite_true, ite_false]
        exact coherentCompositionBackwardMap t hi hj _
      · simp only [coherentCompositionObj, Fin.lastCases_castSucc, hi, hj, ite_false]
        exact toUnit _ ≫ eId SSet Y

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
