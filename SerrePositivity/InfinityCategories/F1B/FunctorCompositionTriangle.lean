module

public import SerrePositivity.InfinityCategories.F1B.FunctorHomSquare
public import SerrePositivity.InfinityCategories.Core.InvertibleEdgeLifting

/-!
概要：h Fun の合成の等式を、指定した三辺を持つ実際の三角形へ戻す。
方針：quasicategory の Hom の合成判定を関手単体集合へ適用する。
規約：三辺のホモトピー代表を保持し、単位・余単位の存在は仮定しない。
使われ方：標準単位比較の合成三角形を固定し、導来 fiber からの逆向きの構成に使う。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：三つのホモトピーの合成を表す関手単体集合の三角形。
方針：実際の二単体を区間からの三辺の curry とともに保持する。
規約：第 0 面が後の辺、第 1 面が合成辺、第 2 面が前の辺。
使われ方：単位の代表を固定した coherent な合成図式。 -/
structure FunctorCompositionTriangle {A X : SSet.{u}} {U V W : A ⟶ X}
    (l : SSet.Homotopy U V) (r : SSet.Homotopy V W) (d : SSet.Homotopy U W) where
  diagram : (Δ[2] : SSet.{u}) ⟶ (ihom A).obj X
  face_zero : stdSimplex.δ (0 : Fin 3) ≫ diagram = curry r.h
  face_one : stdSimplex.δ (1 : Fin 3) ≫ diagram = curry d.h
  face_two : stdSimplex.δ (2 : Fin 3) ≫ diagram = curry l.h

/-- 概要：h Fun での合成関係は指定した三辺を持つ実際の三角形で表せる。
方針：三辺の代表を固定した合成三角形の存在を関手単体集合に適用する。
規約：X の quasicategory 性だけを仮定し、A は任意。
使われ方：写像空間の標準単位比較を三角形の合成として実現する。 -/
lemma nonempty_functorCompositionTriangle_of_homEq {A X : SSet.{u}} [Quasicategory X]
    {U V W : A ⟶ X} (l : SSet.Homotopy U V) (r : SSet.Homotopy V W)
    (d : SSet.Homotopy U W)
    (h : SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy l) ≫
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy r) =
        SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy d)) :
    Nonempty (FunctorCompositionTriangle l r d) := by
  obtain ⟨t⟩ := compStruct_nonempty_of_homMk_fac h
  refine ⟨⟨SSet.yonedaEquiv.symm t.simplex, ?_, ?_, ?_⟩⟩
  · apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact t.d₀
  · apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact t.d₁
  · apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, Equiv.apply_symm_apply]
    exact t.d₂

/-- 概要：合成三角形をパラメータの射に沿って制限する。
方針：関手単体集合の前合成を図式に後合成し、三辺の raw な前合成条件を使う。
規約：新しい三角形を選ばず、与えられた三角形そのものを制限する。
使われ方：普遍合成三角形から任意の族の合成図式を得る。 -/
noncomputable def FunctorCompositionTriangle.precomp {A B X : SSet.{u}}
    {U V W : A ⟶ X} {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d : SSet.Homotopy U W} (T : FunctorCompositionTriangle l r d) (i : B ⟶ A)
    (l' : SSet.Homotopy (i ≫ U) (i ≫ V)) (r' : SSet.Homotopy (i ≫ V) (i ≫ W))
    (d' : SSet.Homotopy (i ≫ U) (i ≫ W))
    (hl : l'.h = (i ▷ (Δ[1] : SSet.{u})) ≫ l.h)
    (hr : r'.h = (i ▷ (Δ[1] : SSet.{u})) ≫ r.h)
    (hd : d'.h = (i ▷ (Δ[1] : SSet.{u})) ≫ d.h) :
    FunctorCompositionTriangle l' r' d' where
  diagram := T.diagram ≫ (pre i).app X
  face_zero := by
    rw [← Category.assoc, T.face_zero]
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
    exact hr.symm
  face_one := by
    rw [← Category.assoc, T.face_one]
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
    exact hd.symm
  face_two := by
    rw [← Category.assoc, T.face_two]
    apply uncurry_injective
    rw [uncurry_pre_app, uncurry_curry, uncurry_curry]
    exact hl.symm

end SerrePositivity.InfinityCategories
