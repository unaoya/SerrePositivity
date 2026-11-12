module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.CompositionHom

/-!
概要：三対象の coherent な合成の Hom を標準対象の表示へ揃える。
方針：二値ラベルと最後の頂点で対象の等号を指定し、Hom の座標を計算する。
規約：等号による移送を明示する。
使われ方：パラメーター付きの標準合成 simplex の単位・合成の証明。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：最後の対象を標準の Z に同定する。
方針：対象の分岐と等号による Hom の移送を計算する。
規約：三対象が異なるとは仮定しない。
使われ方：三対象の標準合成 simplex の座標。 -/
lemma coherentCompositionObj_last {C : Type v} (X Y Z : C) (n : ℕ)
    (t : Fin (n + 1) →o Fin 2) : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t (Fin.last (n + 1)) = Z := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj, Fin.lastCases_last]

/-- 概要：零ラベルの対象を標準の X に同定する。
方針：対象の分岐と等号による Hom の移送を計算する。
規約：三対象が異なるとは仮定しない。
使われ方：三対象の標準合成 simplex の座標。 -/
lemma coherentCompositionObj_zero {C : Type v} (X Y Z : C) {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i = 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t i.castSucc = X := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj, Fin.lastCases_castSucc, hi, ite_true]

/-- 概要：一ラベルの対象を標準の Y に同定する。
方針：対象の分岐と等号による Hom の移送を計算する。
規約：三対象が異なるとは仮定しない。
使われ方：三対象の標準合成 simplex の座標。 -/
lemma coherentCompositionObj_one {C : Type v} (X Y Z : C) {n : ℕ}
    (t : Fin (n + 1) →o Fin 2) (i : Fin (n + 1)) (hi : t i ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj X Y Z t i.castSucc = Y := by
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionObj, Fin.lastCases_castSucc, hi, ite_false]

/-- 概要：最後の自己 Hom の座標は Z の恒等。
方針：対象の分岐と等号による Hom の移送を計算する。
規約：三対象が異なるとは仮定しない。
使われ方：三対象の標準合成 simplex の座標。 -/
lemma coherentCompositionHom_last_last {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t (Fin.last (n + 1)) (Fin.last (n + 1)) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom (coherentCompositionObj_last X Y Z n t)
          (coherentCompositionObj_last X Y Z n t)) = toUnit _ ≫ eId SSet Z := by
  simp -implicitDefEqProofs +instances [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, coherentCompositionObj_last,
    Category.assoc]

/-- 概要：零ラベルから最後への座標は二つの豊穣射の合成。
方針：対象の分岐と等号による Hom の移送を計算する。
規約：三対象が異なるとは仮定しない。
使われ方：三対象の標準合成 simplex の座標。 -/
lemma coherentCompositionHom_zero_last {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hi : t i = 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t i.castSucc (Fin.last (n + 1)) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom (coherentCompositionObj_zero X Y Z t i hi)
          (coherentCompositionObj_last X Y Z n t)) =
      lift (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi (Fin.last (n + 1)) ≫ SSet.yonedaEquiv.symm σ)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm τ) ≫ eComp SSet X Y Z := by
  simp -implicitDefEqProofs +instances [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, coherentCompositionObj_zero,
    coherentCompositionObj_last, hi, Category.assoc]

/-- 概要：一ラベルから最後への座標は二番目の豊穣射。
方針：対象の分岐と等号による Hom の移送を計算する。
規約：三対象が異なるとは仮定しない。
使われ方：三対象の標準合成 simplex の座標。 -/
lemma coherentCompositionHom_one_last {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i : Fin (n + 1)) (hi : t i ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t i.castSucc (Fin.last (n + 1)) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom (coherentCompositionObj_one X Y Z t i hi)
          (coherentCompositionObj_last X Y Z n t)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm τ := by
  simp -implicitDefEqProofs +instances [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, coherentCompositionObj_one,
    coherentCompositionObj_last, hi, Category.assoc]

/-- 概要：零ラベル間の座標は X の恒等。
方針：対象の分岐と等号による Hom の移送を計算する。
規約：三対象が異なるとは仮定しない。
使われ方：三対象の標準合成 simplex の座標。 -/
lemma coherentCompositionHom_zero_zero {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j = 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t i.castSucc j.castSucc ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom (coherentCompositionObj_zero X Y Z t i hi)
          (coherentCompositionObj_zero X Y Z t j hj)) =
      toUnit _ ≫ eId SSet X := by
  simp -implicitDefEqProofs +instances [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, coherentCompositionObj_zero,
    coherentCompositionObj_zero, hi, hj, Category.assoc]

/-- 概要：零から一への座標は最初の豊穣射。
方針：対象の分岐と等号による Hom の移送を計算する。
規約：三対象が異なるとは仮定しない。
使われ方：三対象の標準合成 simplex の座標。 -/
lemma coherentCompositionHom_zero_one {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i = 0) (hj : t j ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t i.castSucc j.castSucc ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom (coherentCompositionObj_zero X Y Z t i hi)
          (coherentCompositionObj_one X Y Z t j hj)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCutMaximumMap t hi j.castSucc ≫ SSet.yonedaEquiv.symm σ := by
  simp -implicitDefEqProofs +instances [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, coherentCompositionObj_zero,
    coherentCompositionObj_one, hi, hj, Category.assoc]

/-- 概要：一ラベル間の座標は Y の恒等。
方針：対象の分岐と等号による Hom の移送を計算する。
規約：三対象が異なるとは仮定しない。
使われ方：三対象の標準合成 simplex の座標。 -/
lemma coherentCompositionHom_one_one {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y Z : C} {n : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (τ : (SimplicialCategory.sHom Y Z) _⦋n⦌) (t : Fin (n + 1) →o Fin 2)
    (i j : Fin (n + 1)) (hi : t i ≠ 0) (hj : t j ≠ 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom σ τ t i.castSucc j.castSucc ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom (coherentCompositionObj_one X Y Z t i hi)
          (coherentCompositionObj_one X Y Z t j hj)) =
      toUnit _ ≫ eId SSet Y := by
  simp -implicitDefEqProofs +instances [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentCompositionHom, coherentCompositionObj_one,
    coherentCompositionObj_one, hi, hj, Category.assoc]

/-- 概要：豊穣合成は三対象の等号による表示変更と可換。
方針：三つの等号を消去する。
規約：表示変更の向きを元の対象から標準対象へ取る。
使われ方：coherent な合成の座標を標準の X・Y・Z へ揃える。 -/
lemma simplicialHom_comp_eqToHom {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {A B D A' B' D' : C} (hA : A = A') (hB : B = B') (hD : D = D') :
    eComp SSet A B D ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hD) =
      (eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) ⊗ₘ
        eqToHom (congrArg₂ SimplicialCategory.sHom hB hD)) ≫ eComp SSet A' B' D' := by
  subst A'
  subst B'
  subst D'
  simp

/-- 概要：三つの Hom の作用の合成則は標準対象へ表示変更してから検査できる。
方針：標的 Hom の表示変更が同型であることと豊穣合成の可換式を使う。
規約：始域の合成 m は任意の単体集合の射。
使われ方：標準合成 simplex の豊穣合成則の座標計算。 -/
lemma simplicialHom_map_comp_iff_normalized {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {A B D A' B' D' : C}
    (hA : A = A') (hB : B = B') (hD : D = D') {U V W : SSet.{u}}
    (m : U ⊗ V ⟶ W) (f : U ⟶ SimplicialCategory.sHom A B)
    (g : V ⟶ SimplicialCategory.sHom B D) (h : W ⟶ SimplicialCategory.sHom A D) :
    m ≫ h = (f ⊗ₘ g) ≫ eComp SSet A B D ↔
      m ≫ (h ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hD)) =
        ((f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB)) ⊗ₘ
          (g ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hB hD))) ≫
            eComp SSet A' B' D' := by
  have he : ((f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB)) ⊗ₘ
        (g ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hB hD))) ≫ eComp SSet A' B' D' =
      ((f ⊗ₘ g) ≫ eComp SSet A B D) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom hA hD) := by
    rw [← tensorHom_comp_tensorHom, Category.assoc, ← simplicialHom_comp_eqToHom hA hB hD,
      ← Category.assoc]
  rw [he, ← Category.assoc, cancel_mono]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
