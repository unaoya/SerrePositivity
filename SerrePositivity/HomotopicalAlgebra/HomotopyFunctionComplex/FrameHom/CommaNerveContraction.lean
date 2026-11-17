module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonSimplex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.DiagramComparisons.CostructuredArrowDiagram
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ElementsChainLifting
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneHomotopyLocalization

/-!
# costructured arrow の射列を最後の頂点で収縮する

概要：CostructuredArrow p d の射列をラベルとする要素圏の各成分を収縮する。
方針：元の射列の最後の頂点の像を基底に選び、各頂点から最後への射で復元する。
規約：添字・値の宇宙を分け、元の全射列と構造射を保持する。
使われ方：Thomason 比較の証明に挟む comma 図式の各行の収縮。
-/

@[expose] public section
universe uE vE uD vD
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open _root_.CategoryTheory

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve

variable {E : Type uE} [Category.{vE} E] {D : Type uD} [Category.{vD} D]
  (p : E ⥤ D) (n : ℕ)

/-- 元の comma の n 射列をラベルとする図式。 -/
abbrev values := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram p) n

/-- ラベルの元の E の射列。 -/
abbrev chain (e : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.values p n).Elements) : ComposableArrows E n :=
  e.val ⋙ CostructuredArrow.proj p e.obj

/-- 基底の移送は元の E の全射列を変更しない。 -/
lemma chain_map {e e' : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.values p n).Elements} (f : e ⟶ e') :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.chain p n e = _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.chain p n e' :=
  congrArg (fun q => q ⋙ CostructuredArrow.proj p e'.obj) f.map_val

/-- 最後の頂点の像を基底とする標準の comma 射列。 -/
def lift (q : ComposableArrows E n) :
    ComposableArrows (CostructuredArrow p (p.obj (q.obj (Fin.last n)))) n where
  obj j := CostructuredArrow.mk (p.map (q.map (homOfLE (Fin.le_last j))))
  map {i j} h := CostructuredArrow.homMk (q.map h) (by
    change p.map (q.map h) ≫ p.map (q.map (homOfLE (Fin.le_last j))) =
      p.map (q.map (homOfLE (Fin.le_last i)))
    rw [← p.map_comp, ← q.map_comp]
    rfl)
  map_id j := by apply CostructuredArrow.hom_ext; exact q.map_id j
  map_comp h l := by apply CostructuredArrow.hom_ext; exact q.map_comp h l

/-- 各元の E の射列から選ぶ同じ標準要素。 -/
def initial (q : ComposableArrows E n) : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.values p n).Elements :=
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.values p n).elementsMk (p.obj (q.obj (Fin.last n))) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.lift p n q)

/-- 標準の comma 射列と最後の構造射から元のラベルを厳密に復元。 -/
lemma lift_reconstruct (e : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.values p n).Elements) :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.lift p n (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.chain p n e) ⋙
        CostructuredArrow.map (e.val.obj (Fin.last n)).hom = e.val := by
  refine CategoryTheory.Functor.ext (fun j => CostructuredArrow.obj_ext _ _ rfl ?_) ?_
  · change p.map (𝟙 _) ≫ (e.val.obj j).hom =
      p.map (e.val.map (homOfLE (Fin.le_last j))).left ≫ (e.val.obj (Fin.last n)).hom
    rw [p.map_id, Category.id_comp]
    exact (CostructuredArrow.w _).symm
  · intro i j h
    apply CostructuredArrow.hom_ext
    simp only [Functor.comp_map, CostructuredArrow.comp_left,
      CostructuredArrow.eqToHom_left, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- 元の射列の標準要素への復元を全射に関手的に行う。 -/
def retraction : (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.values p n).Elements ⥤ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.values p n).Elements where
  obj e := _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.initial p n (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.chain p n e)
  map f := eqToHom (congrArg (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.initial p n) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.chain_map p n f))
  map_id _ := rfl
  map_comp _ _ := by simp only [eqToHom_trans]

/-- 各標準要素から元の要素への同じ最後の構造射による収縮。 -/
def contraction : _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.retraction p n ⟶ 𝟭 _ where
  app e := Functor.Elements.homMk (e.val.obj (Fin.last n)).hom (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.lift_reconstruct p n e)
  naturality {e e'} f := by
    apply Functor.Elements.hom_ext
    change (eqToHom (congrArg (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.initial p n) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.chain_map p n f))).hom ≫
      (e'.val.obj (Fin.last n)).hom = (e.val.obj (Fin.last n)).hom ≫ f.hom
    rw [_root_.SerrePositivity.LabelledChain.eqToHom_hom]
    have h := eqToHom_naturality
      (fun q : ComposableArrows (CostructuredArrow p e'.obj) n =>
        (q.obj (Fin.last n)).hom) f.map_val
    dsimp [_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve.values, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values, _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.nerveDiagram, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram,
      nerveFunctor, nerveMap, CostructuredArrow.map] at h
    simpa only [eqToHom_refl, Category.comp_id] using h.symm

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.CommaNerve
