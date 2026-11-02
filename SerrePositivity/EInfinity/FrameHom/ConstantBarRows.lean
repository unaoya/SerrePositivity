module

public import SerrePositivity.EInfinity.FrameHom.BarRowsCoproduct
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# 定値図式の要素圏の各行の収縮

概要：定値図式の bar の各行を最初のラベルへ射影し、始対象で収縮する。
方針：ラベルを保って基底を始対象へ戻す関手と、その元の自然変換を使う。
規約：値と添字の宇宙は独立。単体集合のモデル構造は仮定しない。
使われ方：定値図式の bar の元の値への augmentation の反転性。
-/

@[expose] public section
universe v uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.EInfinity.FrameHom.ConstantBar
open SerrePositivity.SimplicialModel

variable (D : Type uD) [Category.{vD} D] (X : Type v)

/-- 同じラベルを全基底対象に置いた元の定値図式。 -/
abbrev values : D ⥤ Type v := (Functor.const D).obj X

/-- 定値図式の射列の全頂点のラベルは最初のラベルと一致する。 -/
lemma first_label {n : ℕ} (e : ComposableArrows (values D X).Elements n)
    (j : Fin (n + 1)) : (e.obj 0).val = (e.obj j).val :=
  (e.map (homOfLE (Fin.zero_le j))).map_val

/-- nerve の元の射列を最初のラベルへ射影する。 -/
def projection : nerve (values D X).Elements ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{max uD vD} X) where
  app _ := ↾fun e => ⟨(e.obj 0).val⟩
  naturality {m n} θ := by
    ext e
    exact congrArg ULift.up (first_label D X e (θ.unop.toOrderHom 0)).symm

/-- 指定した基底対象の同じラベルで一定の射列。 -/
def inclusion (i : D) :
    (Functor.const SimplexCategoryᵒᵖ).obj (ULift.{max uD vD} X) ⟶
      nerve (values D X).Elements where
  app _ := ↾fun x => (Functor.const _).obj ((values D X).elementsMk i x.down)
  naturality _ _ _ := rfl

/-- 同じ指定ラベルへの射影は包含の左逆。 -/
lemma inclusion_projection (i : D) : inclusion D X i ≫ projection D X = 𝟙 _ := rfl

/-- ラベルを保存し、基底を指定した対象へ戻す元の要素圏の関手。 -/
def retraction (i : D) : (values D X).Elements ⥤ (values D X).Elements where
  obj e := (values D X).elementsMk i e.val
  map f := Functor.Elements.homMk (𝟙 i) f.map_val
  map_id _ := by apply Functor.Elements.hom_ext; rfl
  map_comp _ _ := by apply Functor.Elements.hom_ext; exact (Category.id_comp _).symm

/-- 射影と包含の合成は、同じ要素圏の関手の nerve に厳密に等しい。 -/
lemma projection_inclusion (i : D) :
    projection D X ≫ inclusion D X i = nerveMap (retraction D X i) := by
  ext n e
  apply LabelledChain.ext_of_first (values D X)
  · rfl
  · rfl

/-- 指定した対象が始対象なら、元の各要素へラベルを保って戻れる。 -/
def contraction {i : D} (hi : IsInitial i) : retraction D X i ⟶ 𝟭 _ where
  app e := Functor.Elements.homMk (hi.to e.obj) rfl
  naturality _ _ _ := by
    apply Functor.Elements.hom_ext
    exact hi.hom_ext _ _

/-- 元の行の射影そのものは、始対象の収縮により局所化で可逆。 -/
lemma projection_localized_isIso {i : D} (hi : IsInitial i) :
    IsIso (AnodyneHomotopy.anodyneQ.map (projection D X)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max uD vD v}
  let e : Q.obj (nerve (values D X).Elements) ≅
      Q.obj ((Functor.const SimplexCategoryᵒᵖ).obj (ULift.{max uD vD} X)) :=
    { hom := Q.map (projection D X)
      inv := Q.map (inclusion D X i)
      hom_inv_id := by
        rw [← Q.map_comp, projection_inclusion]
        have h := AnodyneHomotopy.map_homotopy_eq Q
          (Localization.inverts _ SSet.anodyneExtensions)
          (NerveHomotopy.homotopy (contraction D X hi))
        exact h.trans (Q.map_id _)
      inv_hom_id := by rw [← Q.map_comp, inclusion_projection, Q.map_id] }
  exact e.isIso_hom

end SerrePositivity.EInfinity.FrameHom.ConstantBar
