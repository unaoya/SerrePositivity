module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerveContraction
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBarAugmentation

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
open _root_.CategoryTheory

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve
open _root_.SerrePositivity.SimplicialModel

variable {E : Type uE} [Category.{vE} E] {D : Type uD} [Category.{vD} D]
  (p : E ⥤ D) (n : ℕ)

/-- 各行で元の E の射列へ射影する。 -/
def projection : nerve (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.values p n).Elements ⟶
    (Functor.const SimplexCategoryᵒᵖ).obj
      (ULift.{max uD vD} (ComposableArrows E n)) where
  app _ := ↾fun c => ⟨_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.chain p n (c.obj 0)⟩
  naturality {m l} θ := by
    ext c
    exact congrArg ULift.up (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.chain_map p n (c.map
      (homOfLE (Fin.zero_le (θ.unop.toOrderHom 0))))).symm

/-- 元の E の射列を最後の頂点で一定の標準要素へ送る。 -/
def inclusion :
    (Functor.const SimplexCategoryᵒᵖ).obj
      (ULift.{max uD vD} (ComposableArrows E n)) ⟶ nerve (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.values p n).Elements where
  app _ := ↾fun q => (Functor.const _).obj (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.initial p n q.down)
  naturality _ _ _ := rfl

/-- 射影は標準要素の包含の左逆。 -/
lemma inclusion_projection : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.inclusion p n ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.projection p n = 𝟙 _ := rfl

/-- 射影と包含の逆向きの合成は、元の収縮関手の nerve。 -/
lemma projection_inclusion :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.projection p n ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.inclusion p n = nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.retraction p n) := by
  ext m c
  change (Functor.const _).obj (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.initial p n (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.chain p n (c.obj 0))) = c ⋙ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.retraction p n
  refine CategoryTheory.Functor.ext (fun j =>
    congrArg (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.initial p n) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.chain_map p n (c.map (homOfLE (Fin.zero_le j))))) ?_
  intro i j h
  dsimp only [Functor.const, Functor.comp_map, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.retraction]
  simp only [eqToHom_trans, eqToHom_refl]

/-- 元の E の射列への行の射影そのものは、同じ収縮により反転される。 -/
lemma projection_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.projection p n)) := by
  let Q := AnodyneHomotopy.anodyneQ.{max uE vE uD vD}
  let e : Q.obj (nerve (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.values p n).Elements) ≅
      Q.obj ((Functor.const SimplexCategoryᵒᵖ).obj
        (ULift.{max uD vD} (ComposableArrows E n))) :=
    { hom := Q.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.projection p n)
      inv := Q.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.inclusion p n)
      hom_inv_id := by
        rw [← Q.map_comp, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.projection_inclusion]
        have h := AnodyneHomotopy.map_homotopy_eq Q
          (Localization.inverts _ SSet.anodyneExtensions)
          (_root_.SerrePositivity.NerveHomotopy.homotopy (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.contraction p n))
        exact h.trans (Q.map_id _)
      inv_hom_id := by rw [← Q.map_comp, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.inclusion_projection, Q.map_id] }
  exact e.isIso_hom

/-- 各行の射影は全係数作用素に自然。 -/
def projectionRows :
    (BarConstruction.rows D).obj (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveDiagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram p)) ⟶
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.labels D (nerve E) where
  app n := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.projection p n.unop.len
  naturality _ _ _ := by ext m c; rfl

/-- comma 図式の元の bar から、同じ圏の nerve の宇宙拡大への射。 -/
def barProjection :
    (BarConstruction.functor D).obj (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveDiagram (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram p)) ⟶
      SSet.uliftFunctor.{max uD vD, max uE vE}.obj (nerve E) :=
  _root_.SerrePositivity.BisimplicialModel.diagonal.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.projectionRows p) ≫
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ConstantBar.labelsDiagonalIso D (nerve E)).hom

/-- 全次数で、最初のラベルの同じ元の E の射列を返す。 -/
lemma barProjection_app (k : SimplexCategoryᵒᵖ)
    (c : ComposableArrows (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.values p k.unop.len).Elements k.unop.len) :
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.barProjection p).app k c = ULift.up (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.chain p k.unop.len (c.obj 0)) := rfl

/-- 同じ comma 図式の bar の元の射影そのものは、局所化で可逆。 -/
lemma barProjection_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.barProjection p)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map
      (_root_.SerrePositivity.BisimplicialModel.diagonal.map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.projectionRows p))) :=
    _root_.SerrePositivity.BisimplicialModel.localized_diagonal_map (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.projectionRows p)
      (fun n => _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.projection_localized_isIso p n.unop.len)
  dsimp only [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.barProjection]
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve
