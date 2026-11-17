module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.ComonadResolutionOperators

/-!
# Comonad 解像の冪と全作用素の係数自然性

概要：Dwyer–Kan の自由解像を係数の射に関手的にする一般界面を構成する。
方針：冪の射を反復し、余単位・対角の自然性を全ての面・退化へ移す。
規約：一般の圏と comonad のみを使い、モデル構造は要求しない。
使われ方：自由単体的局所化へ相対関手を送る。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution

open _root_.CategoryTheory
open _root_.SerrePositivity.HomotopyFunctionComplex.ComonadResolutionOperators

variable {C : Type u} [Category.{v} C] (G : Comonad C)

/-- 概要：同じ comonad の反復冪に元の射を送る（Dwyer–Kan）。
方針：零回は元の射、後続は同じ G.map で定義する。
規約：元の comonad と全反復を保持する。
使われ方：解像の係数射の各次数の成分。 -/
def powerMap {X Y : C} (f : X ⟶ Y) : (n : ℕ) → power G X n ⟶ power G Y n
  | 0 => f
  | n + 1 => G.map (powerMap f n)

/-- 概要：反復冪の射は恒等射を保つ（Dwyer–Kan）。
方針：同じ G の恒等則を反復する。
規約：全次数の厳密な等式。
使われ方：解像を係数に関して関手にする。 -/
lemma powerMap_id (X : C) (n : ℕ) : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G (𝟙 X) n = 𝟙 (power G X n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change G.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G (𝟙 X) n) = 𝟙 (G.obj (power G X n))
    rw [ih]
    exact G.map_id _

/-- 概要：反復冪の射は合成を保つ（Dwyer–Kan）。
方針：同じ G の合成則を反復する。
規約：全次数で元の合成順序を保持する。
使われ方：解像の係数関手の合成。 -/
lemma powerMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (n : ℕ) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G (f ≫ g) n = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f n ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap, ih, CategoryTheory.Functor.map_comp]

/-- 概要：解像の全ての面は元の係数射に自然（Dwyer–Kan）。
方針：最外面は余単位の自然性、内側の面は G.map と帰納を使う。
規約：六つの単体関係式を変更しない。
使われ方：全単体作用素に自然な係数比較。 -/
lemma face_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) (i : Fin (n + 1)) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 1) ≫ face G Y n i = face G X n i ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f n := by
  induction n with
  | zero => fin_cases i; exact G.ε.naturality f
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      change G.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 1)) ≫ G.ε.app (power G Y (n + 1)) =
        G.ε.app (power G X (n + 1)) ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 1)
      exact G.ε.naturality _
    | succ i =>
      change G.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 1)) ≫ G.map (face G Y n i) =
        G.map (face G X n i) ≫ G.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f n)
      rw [← G.map_comp, ← G.map_comp, ih i]

/-- 概要：解像の全ての退化は元の係数射に自然（Dwyer–Kan）。
方針：最外退化は対角の自然性、内側の退化は G.map と帰納を使う。
規約：全次数の全ての退化を含む。
使われ方：係数関手の全退化作用素との整合性。 -/
lemma degeneracy_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) (i : Fin (n + 1)) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 1) ≫ degeneracy G Y n i =
      degeneracy G X n i ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 2) := by
  induction n with
  | zero => fin_cases i; exact G.δ.naturality f
  | succ n ih =>
    induction i using Fin.cases with
    | zero =>
      change G.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 1)) ≫ G.δ.app (power G Y (n + 1)) =
        G.δ.app (power G X (n + 1)) ≫ G.map (G.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 1)))
      exact G.δ.naturality _
    | succ i =>
      change G.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 1)) ≫ G.map (degeneracy G Y n i) =
        G.map (degeneracy G X n i) ≫ G.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f (n + 2))
      rw [← G.map_comp, ← G.map_comp, ih i]

/-- 概要：元の augmentation は全反復の係数射に自然（Dwyer–Kan）。
方針：逐次合成の定義と同じ余単位の自然性を使う。
規約：元の augmentation を保持する。
使われ方：係数射が固定対象の表示を保つことの証明。 -/
lemma augmentation_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f n ≫ augmentation G Y n = augmentation G X n ≫ f := by
  induction n with
  | zero =>
    change f ≫ 𝟙 Y = 𝟙 X ≫ f
    rw [Category.comp_id, Category.id_comp]
  | succ n ih =>
    change G.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution.powerMap G f n) ≫ (G.ε.app (power G Y n) ≫ augmentation G Y n) =
      (G.ε.app (power G X n) ≫ augmentation G X n) ≫ f
    rw [← Category.assoc, G.ε.naturality, Functor.id_map, Category.assoc, ih,
      Category.assoc]

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ComonadResolution
