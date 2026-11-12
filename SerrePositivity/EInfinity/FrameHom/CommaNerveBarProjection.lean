module

public import SerrePositivity.EInfinity.FrameHom.CommaNerveContraction
public import SerrePositivity.EInfinity.FrameHom.ConstantBarAugmentation

/-!
# comma 図式の bar から元の圏の nerve への射影の反転

概要：任意の p : E → D で、CostructuredArrow p の nerve の bar を元の nerve E へ送る。
方針：各行で元の射列への射影と最後の頂点による収縮を使い、対角で反転性を得る。
規約：元の射列・構造射・全単体作用素を保つ。単体集合モデルは仮定しない。
使われ方：Thomason 比較の証明に挟む comma 図式の全体の射影。
-/

@[expose] public section
universe uE vE uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory

namespace SerrePositivity.EInfinity.FrameHom.CommaNerve
open SerrePositivity.SimplicialModel

variable {E : Type uE} [Category.{vE} E] {D : Type uD} [Category.{vD} D]
  (p : E ⥤ D) (n : ℕ)

/-- 各行で元の E の射列へ射影する。 -/
def projection : nerve (values p n).Elements ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj
      (ULift.{max uD vD} (ComposableArrows E n)) where
  app _ := ↾fun c => ⟨chain p n (c.obj 0)⟩
  naturality {m l} θ := by
    ext c
    exact congrArg ULift.up (chain_map p n (c.map
      (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0))))).symm

/-- 元の E の射列を最後の頂点で一定の標準要素へ送る。 -/
def inclusion :
    (Functor.const SimplexCategoryᵒᵖ).obj
      (ULift.{max uD vD} (ComposableArrows E n)) ⟶ nerve (values p n).Elements where
  app _ := ↾fun q => (Functor.const _).obj (initial p n q.down)
  naturality _ _ _ := rfl

/-- 射影は標準要素の包含の左逆。 -/
lemma inclusion_projection : inclusion p n ≫ projection p n = 𝟙 _ := rfl

/-- 射影と包含の逆向きの合成は、元の収縮関手の nerve。 -/
lemma projection_inclusion :
    projection p n ≫ inclusion p n = nerveMap (retraction p n) := by
  ext m c
  change (Functor.const _).obj (initial p n (chain p n (c.obj 0))) = c ⋙ retraction p n
  refine CategoryTheory.Functor.ext (fun j =>
    congrArg (initial p n) (chain_map p n (c.map (homOfLE (Fin.zero_le j))))) ?_
  intro i j h
  dsimp only [Functor.const, Functor.comp_map, retraction]
  simp only [eqToHom_trans, eqToHom_refl]

/-- 元の E の射列への行の射影そのものは、同じ収縮により反転される。 -/
lemma projection_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (projection p n)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max uE vE uD vD}
  let e : Q.obj (nerve (values p n).Elements) ≅
      Q.obj ((Functor.const SimplexCategoryᵒᵖ).obj
        (ULift.{max uD vD} (ComposableArrows E n))) :=
    { hom := Q.map (projection p n)
      inv := Q.map (inclusion p n)
      hom_inv_id := by
        rw [← Q.map_comp, projection_inclusion]
        have h := AnodyneHomotopy.map_homotopy_eq Q
          (Localization.inverts _ SSet.anodyneExtensions)
          (NerveHomotopy.homotopy (contraction p n))
        exact h.trans (Q.map_id _)
      inv_hom_id := by rw [← Q.map_comp, inclusion_projection, Q.map_id] }
  exact e.isIso_hom

/-- 各行の射影は全係数作用素に自然。 -/
def projectionRows :
    (BarConstruction.rows D).obj (Thomason.nerveDiagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram p)) ⟶
      ConstantBar.labels D (nerve E) where
  app n := projection p n.unop.len
  naturality _ _ _ := by ext m c; rfl

/-- comma 図式の元の bar から、同じ圏の nerve の宇宙拡大への射。 -/
def barProjection :
    (BarConstruction.functor D).obj (Thomason.nerveDiagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram p)) ⟶
      SSet.uliftFunctor.{max uD vD, max uE vE}.obj (nerve E) :=
  BisimplicialModel.diagonal.map (projectionRows p) ≫
    (ConstantBar.labelsDiagonalIso D (nerve E)).hom

/-- 全次数で、最初のラベルの同じ元の E の射列を返す。 -/
lemma barProjection_app (k : SimplexCategoryᵒᵖ)
    (c : ComposableArrows (values p k.unop.len).Elements k.unop.len) :
    (barProjection p).app k c = ULift.up (chain p k.unop.len (c.obj 0)) := rfl

/-- 同じ comma 図式の bar の元の射影そのものは、局所化で可逆。 -/
lemma barProjection_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (barProjection p)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (BisimplicialModel.diagonal.map (projectionRows p))) :=
    BisimplicialModel.localized_diagonal_map (projectionRows p)
      (fun n => projection_localized_isIso p n.unop.len)
  dsimp only [barProjection]
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.EInfinity.FrameHom.CommaNerve
