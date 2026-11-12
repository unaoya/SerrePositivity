module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionSimplex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.HomReindex

/-!
概要：豊穣な合成 simplex の二つの定数ラベルでの両端。
方針：一側は二番目の Hom 比較、零側は二つの射の豊穣合成の Hom 比較と同定する。
規約：比較は coherent な単体そのものの等式。
使われ方：普遍 pointed-space 輸送に使う標準 prism の両端の指定。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：ラベルが全て零なら切替前の最大座標は通常の最後以前の最大座標。
方針：二つの座標集合の等式を使う。
規約：path は追加した最後の頂点で終わる。
使われ方：合成 simplex の零側の計算。 -/
lemma pathCutMaximum_const_zero {n : ℕ} {i : Fin (n + 1)}
    (P : Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum (OrderHom.const _ 0) rfl P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum P := by
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutBeforeLast (OrderHom.const _ 0) P = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast P := by
    classical
    ext k
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutBeforeLast, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathBeforeLast, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change ((0 : Fin 2) = 0 ∧ _) ↔ _
    simp
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximum _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum
  simp only [h]

/-- 概要：全て零の切替ラベルの座標射は通常の右 Hom の最大座標射。
方針：各旗の各頂点で最大元の等式を使う。
規約：標準単体への射の等式。
使われ方：合成の Hom の零端点を通常の Hom 比較へ移す。 -/
lemma pathCutMaximumMap_const_zero {n : ℕ} (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap (OrderHom.const _ 0) (by rfl) (Fin.last (n + 1)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap.{u} i := by
  apply SSet.hom_ext
  rintro ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  intro P
  apply stdSimplex.ext
  intro k
  exact pathCutMaximum_const_zero (P.obj k)

/-- 概要：同じ標準単体で指定した二つの豊穣射の合成は Yoneda 射の合成と一致する。
方針：Yoneda の自然性を使う。
規約：パラメーターの次数は二つの Hom で共通。
使われ方：合成 simplex の零側の Hom の計算。 -/
lemma simplicialHom_yoneda_comp {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z : C} {n : ℕ} (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) :
    lift (SSet.yonedaEquiv.symm σ) (SSet.yonedaEquiv.symm τ) ≫ eComp SSet X Y Z =
      SSet.yonedaEquiv.symm ((eComp SSet X Y Z).app (Opposite.op ⦋n⦌) (σ, τ)) := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  congr 1
  apply Prod.ext
  · change SSet.yonedaEquiv (SSet.yonedaEquiv.symm σ) = σ
    exact Equiv.apply_symm_apply _ _
  · change SSet.yonedaEquiv (SSet.yonedaEquiv.symm τ) = τ
    exact Equiv.apply_symm_apply _ _

/-- 概要：全て一のラベルの合成 simplex は二番目の Hom の標準比較。
方針：対象と Hom の端点の表示を揃え、恒等部分と非定値部分を計算する。
規約：等式は豊穣関手として成立する。
使われ方：標準輸送 prism の一端点。 -/
lemma coherentCompositionSimplex_one {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z : C} {n : ℕ} (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex σ τ (OrderHom.const _ 1) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex τ := by
  have ho (i : Fin (n + 2)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z (OrderHom.const _ 1) i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj Y Z i := by
    induction i using Fin.lastCases
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last X Y Z n _).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last Y Z n).symm
    · rename_i i
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_one X Y Z _ i (by change (1 : Fin 2) ≠ 0; decide)).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast Y Z i).symm
  apply EnrichedFunctor.ext SSet (fun i ↦ ho i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ (OrderHom.const _ 1) i j ≫ eqToHom _ =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom τ i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last Y Z n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last Y Z n)))).1
    simp only [Category.assoc, eqToHom_trans]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_last_last σ τ _).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_last_last τ).symm
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := Path.le (P.obj 0)
    change n + 1 ≤ j.val at h
    have hj := j.isLt
    change j.val < n + 1 at hj
    omega
  case cast.last i =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast Y Z i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last Y Z n)))).1
    simp only [Category.assoc, eqToHom_trans]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_last σ τ _ i (by change (1 : Fin 2) ≠ 0; decide)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_last τ i).symm
  case cast.cast i j =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast Y Z i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast Y Z j)))).1
    simp only [Category.assoc, eqToHom_trans]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_one_one σ τ _ i j
      (by change (1 : Fin 2) ≠ 0; decide) (by change (1 : Fin 2) ≠ 0; decide)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_cast τ i j).symm

/-- 概要：全て零のラベルの最後へ向かう Hom は二つの豊穣射の標準合成。
方針：二つの座標を同じ最大座標に揃え、Yoneda の合成公式を使う。
規約：始点は追加した最後の頂点と異なる。
使われ方：標準合成 simplex の零端点の非定値 Hom。 -/
lemma coherentCompositionHom_const_zero_last {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (i : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ (OrderHom.const _ 0) i.castSucc (Fin.last (n + 1)) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_zero X Y Z _ i rfl) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last X Y Z n _)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i ≫
        SSet.yonedaEquiv.symm ((eComp SSet X Y Z).app (Opposite.op ⦋n⦌) (σ, τ)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_last σ τ _ i rfl, pathCutMaximumMap_const_zero,
    ← comp_lift, Category.assoc, simplicialHom_yoneda_comp]

/-- 概要：全て零のラベルの合成 simplex は二つの豊穣射の合成の Hom 比較。
方針：対象と Hom の表示を揃え、共通の最大座標で合成を計算する。
規約：coherent な単体そのものの等式。
使われ方：標準輸送 prism の零端点。 -/
lemma coherentCompositionSimplex_zero {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y Z : C} {n : ℕ} (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionSimplex σ τ (OrderHom.const _ 0) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonSimplex ((eComp SSet X Y Z).app (Opposite.op ⦋n⦌) (σ, τ)) := by
  let υ := (eComp SSet X Y Z).app (Opposite.op ⦋n⦌) (σ, τ)
  have ho (i : Fin (n + 2)) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z (OrderHom.const _ 0) i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj X Z i := by
    induction i using Fin.lastCases
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_last X Y Z n _).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Z n).symm
    · rename_i i
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj_zero X Y Z _ i rfl).trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Z i).symm
  apply EnrichedFunctor.ext SSet (fun i ↦ ho i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ (OrderHom.const _ 0) i j ≫ eqToHom _ =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonHom υ i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Z n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Z n)))).1
    simp only [Category.assoc, eqToHom_trans]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_last_last σ τ _).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_last_last υ).symm
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := Path.le (P.obj 0)
    change n + 1 ≤ j.val at h
    have hj := j.isLt
    change j.val < n + 1 at hj
    omega
  case cast.last i =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Z i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Z n)))).1
    simp only [Category.assoc, eqToHom_trans]
    exact (coherentCompositionHom_const_zero_last σ τ i).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_last υ i).symm
  case cast.cast i j =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Z i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Z j)))).1
    simp only [Category.assoc, eqToHom_trans]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom_zero_zero σ τ _ i j rfl rfl).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_cast υ i j).symm

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
