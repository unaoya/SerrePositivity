module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-!
# 固定語の zigzag と全縦弱同値の圏

概要：Dwyer–Kan 1980b §5.1 の固定語・固定端点の hammock graph を構成する。
方針：各頂点と各列の射を保持し、可換正方形をなす縦弱同値を射にする。
規約：後ろ向きの列だけに弱同値を要求し、縦射は両端で恒等射に一致する。
使われ方：語で添字付けた nerve 図式と三本矢からの比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

namespace Word

/-- 各向き付き列の始域となる頂点。 -/
def source (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin w.length) : Fin (w.length + 1) :=
  match w.direction i with
  | .forward => i.castSucc
  | .backward => i.succ

/-- 各向き付き列の終域となる頂点。 -/
def target (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (i : Fin w.length) : Fin (w.length + 1) :=
  match w.direction i with
  | .forward => i.succ
  | .backward => i.castSucc

end Word

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C)

/-- 固定語・固定端点の一列の zigzag。 -/
structure Zigzag where
  vertex : Fin (w.length + 1) → C
  first : vertex 0 = X
  last : vertex (Fin.last w.length) = Y
  arrow : ∀ i, vertex (w.source i) ⟶ vertex (w.target i)
  backward_mem : ∀ i, w.direction i = .backward → W (arrow i)

namespace Zigzag
variable {W w X Y}

/-- 元の全頂点の縦弱同値と、全列の可換性。 -/
structure Hom (S T : Zigzag W w X Y) where
  app : ∀ j, S.vertex j ⟶ T.vertex j
  app_mem : ∀ j, W (app j)
  first : app 0 = eqToHom (S.first.trans T.first.symm)
  last : app (Fin.last w.length) = eqToHom (S.last.trans T.last.symm)
  comm : ∀ i, S.arrow i ≫ app (w.target i) = app (w.source i) ≫ T.arrow i

@[ext] lemma hom_ext {S T : Zigzag W w X Y} (f g : Hom S T)
    (h : ∀ j, f.app j = g.app j) : f = g := by
  have : f.app = g.app := funext h
  cases f
  cases g
  cases this
  rfl

/-- 全縦射を成分ごとに合成する、固定語の zigzag の圏。 -/
instance zigzagCategory [W.IsMultiplicative] : Category.{v} (Zigzag W w X Y) where
  Hom := Hom
  id S :=
    { app j := 𝟙 (S.vertex j)
      app_mem j := W.id_mem _
      first := by simp
      last := by simp
      comm i := by simp }
  comp f g :=
    { app j := f.app j ≫ g.app j
      app_mem j := W.comp_mem _ _ (f.app_mem j) (g.app_mem j)
      first := by rw [f.first, g.first, eqToHom_trans]
      last := by rw [f.last, g.last, eqToHom_trans]
      comm i := by rw [← Category.assoc, f.comm, Category.assoc, g.comm, ← Category.assoc] }
  id_comp f := hom_ext _ _ (fun _ => Category.id_comp _)
  comp_id f := hom_ext _ _ (fun _ => Category.comp_id _)
  assoc f g h := hom_ext _ _ (fun _ => Category.assoc _ _ _)

variable [W.IsMultiplicative]

@[simp] lemma id_app (S : Zigzag W w X Y) (j : Fin (w.length + 1)) :
    (𝟙 S : S ⟶ S).app j = 𝟙 (S.vertex j) := rfl

@[simp] lemma comp_app {S T U : Zigzag W w X Y} (f : S ⟶ T) (g : T ⟶ U)
    (j : Fin (w.length + 1)) : (f ≫ g).app j = f.app j ≫ g.app j := rfl

/-- 各固定位置の元の頂点と縦射への射影。 -/
def evaluation (j : Fin (w.length + 1)) : Zigzag W w X Y ⥤ C where
  obj S := S.vertex j
  map f := f.app j

end Zigzag

/-- 固定語の hammock graph は、全縦弱同値の zigzag 圏の nerve。 -/
abbrev graph [W.IsMultiplicative] : SSet.{max u v} := nerve (Zigzag W w X Y)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
