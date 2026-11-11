module

public import SerrePositivity.EInfinity.FrameHom.ThomasonSimplex
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CostructuredArrowDiagram
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
open CategoryTheory

namespace SerrePositivity.EInfinity.FrameHom.CommaNerve

variable {E : Type uE} [Category.{vE} E] {D : Type uD} [Category.{vD} D]
  (p : E ⥤ D) (n : ℕ)

/-- 元の comma の n 射列をラベルとする図式。 -/
abbrev values := Thomason.values (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram p) n

/-- ラベルの元の E の射列。 -/
abbrev chain (e : (values p n).Elements) : ComposableArrows E n :=
  e.val ⋙ CostructuredArrow.proj p e.obj

/-- 基底の移送は元の E の全射列を変更しない。 -/
lemma chain_map {e e' : (values p n).Elements} (f : e ⟶ e') :
    chain p n e = chain p n e' :=
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
def initial (q : ComposableArrows E n) : (values p n).Elements :=
  (values p n).elementsMk (p.obj (q.obj (Fin.last n))) (lift p n q)

/-- 標準の comma 射列と最後の構造射から元のラベルを厳密に復元。 -/
lemma lift_reconstruct (e : (values p n).Elements) :
    lift p n (chain p n e) ⋙
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
def retraction : (values p n).Elements ⥤ (values p n).Elements where
  obj e := initial p n (chain p n e)
  map f := eqToHom (congrArg (initial p n) (chain_map p n f))
  map_id _ := rfl
  map_comp _ _ := by simp only [eqToHom_trans]

/-- 各標準要素から元の要素への同じ最後の構造射による収縮。 -/
def contraction : retraction p n ⟶ 𝟭 _ where
  app e := Functor.Elements.homMk (e.val.obj (Fin.last n)).hom (lift_reconstruct p n e)
  naturality {e e'} f := by
    apply Functor.Elements.hom_ext
    change (eqToHom (congrArg (initial p n) (chain_map p n f))).hom ≫
      (e'.val.obj (Fin.last n)).hom = (e.val.obj (Fin.last n)).hom ≫ f.hom
    rw [LabelledChain.eqToHom_hom]
    have h := eqToHom_naturality
      (fun q : ComposableArrows (CostructuredArrow p e'.obj) n =>
        (q.obj (Fin.last n)).hom) f.map_val
    dsimp [values, Thomason.values, Thomason.nerveDiagram, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.costructuredArrowDiagram,
      nerveFunctor, nerveMap, CostructuredArrow.map] at h
    simpa only [eqToHom_refl, Category.comp_id] using h.symm

end SerrePositivity.EInfinity.FrameHom.CommaNerve
