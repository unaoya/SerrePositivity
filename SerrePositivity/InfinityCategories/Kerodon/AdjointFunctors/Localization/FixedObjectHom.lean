module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.EqToHom

/-!
# 対象の表示を保つ圏の図式の固定 Hom

概要：Dwyer–Kan の次数ごとの局所化の Hom を固定対象で扱う一般界面を作る。
方針：対象表示の等式で元の関手の Hom 作用を前後から移す。
規約：対象表示が全作用素で保たれることを明示的に要求する。
使われ方：固定した両対象の Hom の単体集合と豊穣合成。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section

universe u v w

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom

open CategoryTheory

variable {I : Type v} [Category I] (D : I ⥤ Cat.{u, u}) {O : Type w}
  (p : (i : I) → O → D.obj i)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : O), (D.map θ).toFunctor.obj (p i X) = p j X)

/-- 概要：対象表示の等式で移した元の関手の Hom 作用（Dwyer–Kan）。
方針：元の Hom 作用の前後を同じ対象表示の eqToHom で移す。
規約：新しい射や合成の選択を加えない。
使われ方：固定対象の Hom の単体作用素。 -/
def map {i j : I} (θ : i ⟶ j) {X Y : O} (f : p i X ⟶ p i Y) : p j X ⟶ p j Y :=
  eqToHom (hp θ X).symm ≫ (D.map θ).toFunctor.map f ≫ eqToHom (hp θ Y)

/-- 概要：固定 Hom の作用は恒等作用素を保つ（Dwyer–Kan）。
方針：元の図式の恒等則と eqToHom の恒等則を使う。
規約：対象表示の等式の証明の選択に依存しない。
使われ方：固定 Hom を関手に束ねる。 -/
lemma map_id (i : I) {X Y : O} (f : p i X ⟶ p i Y) :
    map D p hp (𝟙 i) f = f := by
  unfold map
  rw [Functor.congr_hom (congrArg Cat.Hom.toFunctor (D.map_id i)) f]
  simp


/-- 概要：固定 Hom の作用は作用素の合成を保つ（Dwyer–Kan）。
方針：元の図式の厳密な合成則と対象移送の合成則を使う。
規約：すべての合成可能な作用素に対する等式。
使われ方：固定 Hom の全単体恒等式。 -/
lemma map_comp {i j k : I} (θ : i ⟶ j) (φ : j ⟶ k)
    {X Y : O} (f : p i X ⟶ p i Y) :
    map D p hp (θ ≫ φ) f = map D p hp φ (map D p hp θ f) := by
  have h : (D.map (θ ≫ φ)).toFunctor =
      (D.map θ).toFunctor ⋙ (D.map φ).toFunctor :=
    congrArg Cat.Hom.toFunctor (D.map_comp θ φ)
  unfold map
  rw [Functor.congr_hom h f]
  simp only [Functor.comp_map, Functor.map_comp, eqToHom_map, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans]


/-- 概要：固定 Hom の作用は元の恒等射を保つ（Dwyer–Kan）。
方針：元の関手の恒等射保存と移送の順逆を相殺する。
規約：同じ次数の圏の恒等射。
使われ方：豊穣単位の自然性。 -/
lemma map_identity {i j : I} (θ : i ⟶ j) (X : O) :
    map D p hp θ (𝟙 (p i X)) = 𝟙 (p j X) := by
  simp [map]

/-- 概要：固定 Hom の作用は元の射の合成を保つ（Dwyer–Kan）。
方針：元の関手の合成保存と中間対象の移送の順逆を相殺する。
規約：合成は各次数の元の圏の合成。
使われ方：豊穣合成の自然性。 -/
lemma map_composition {i j : I} (θ : i ⟶ j) {X Y Z : O}
    (f : p i X ⟶ p i Y) (g : p i Y ⟶ p i Z) :
    map D p hp θ (f ≫ g) = map D p hp θ f ≫ map D p hp θ g := by
  simp [map, Category.assoc]

/-- 概要：固定した両対象の Hom の関手（Dwyer–Kan）。
方針：元の Hom と対象表示による同じ作用を束ねる。
規約：全作用素で厳密な関手則を持つ。
使われ方：単体圏の場合の Hom の単体集合。 -/
def functor (X Y : O) : I ⥤ Type u where
  obj i := p i X ⟶ p i Y
  map θ := ↾(map D p hp θ)
  map_id i := by
    apply ConcreteCategory.hom_ext
    intro f
    exact map_id D p hp i f
  map_comp θ φ := by
    apply ConcreteCategory.hom_ext
    intro f
    exact map_comp D p hp θ φ f

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FixedObjectHom
