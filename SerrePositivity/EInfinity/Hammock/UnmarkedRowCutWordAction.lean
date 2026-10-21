module

public import SerrePositivity.EInfinity.Hammock.UnmarkedFirstFactorWordActionVertices
public import SerrePositivity.EInfinity.Hammock.UnmarkedFirstFiberCuts
public import SerrePositivity.EInfinity.SimplicialLocalization.UnmarkedFixedCutGeneratorTransport

/-!
# 元の全行の切断の前後の射列と語の圧縮

概要：圧縮後の全行の切断を元の生成矢へ移し、元の接頭射・残りを回収する。
方針：元の生成矢の一致・最小列以前の全行の指定性・固定切断の比較を使う。
規約：元の各行と全射列を保持し、後置区間の指定性を仮定しない。
使われ方：prefix 最終列と残り最初列の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
open CategoryTheory SimplicialLocalization.GeneratorWord

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (graph W.paths a X Y).obj n)
  (h : ∃ i, column W (τ.obj 0) i ≠ [])
  (hT : column W ((τ ⋙ WordAction.functor f).obj 0)
    (f.orderHom (firstColumn W (τ.obj 0) h)) ≠ [])

include hT in
lemma row_cut_left (d : Fin (n.unop.len + 1)) :
    HEq (fixedRowCut W (τ ⋙ WordAction.functor f)
      (f.orderHom (firstColumn W (τ.obj 0) h)) hT d).left
      (Quiver.Path.comp
        (WordActionCut.prefixMap W f (τ.obj d) (f.orderHom (firstColumn W (τ.obj 0) h))
          (firstColumn W (τ.obj 0) h) rfl
          ((f.direction_eq _).trans (firstColumn_forward W (τ.obj 0) h)))
        (fixedRowCut W τ (firstColumn W (τ.obj 0) h)
          (firstColumn_nonempty W (τ.obj 0) h) d).left) := by
  let Q := fixedRowCut W (τ ⋙ WordAction.functor f)
    (f.orderHom (firstColumn W (τ.obj 0) h)) hT d
  let Q' := FixedCut.changeGenerator W (generator_eq W f τ h hT) Q
  have hc := WordActionCut.cut_left W f (τ.obj d)
    (f.orderHom (firstColumn W (τ.obj 0) h)) (firstColumn W (τ.obj 0) h)
    rfl ((f.direction_eq _).trans (firstColumn_forward W (τ.obj 0) h))
    (fun k _ hk => before_firstColumn_row_mem W τ h d k hk)
    (fixedRowCut W τ (firstColumn W (τ.obj 0) h) (firstColumn_nonempty W (τ.obj 0) h) d) Q'
  exact (FixedCut.changeGenerator_left W (generator_eq W f τ h hT) Q).symm.trans hc

include hT in
lemma row_cut_right (d : Fin (n.unop.len + 1)) :
    HEq (fixedRowCut W (τ ⋙ WordAction.functor f)
      (f.orderHom (firstColumn W (τ.obj 0) h)) hT d).right
      ((fixedRowCut W τ (firstColumn W (τ.obj 0) h)
        (firstColumn_nonempty W (τ.obj 0) h) d).right.comp
        (WordActionCut.residual W f (τ.obj d) (f.orderHom (firstColumn W (τ.obj 0) h))
          (firstColumn W (τ.obj 0) h) rfl
          ((f.direction_eq _).trans (firstColumn_forward W (τ.obj 0) h)))) := by
  let Q := fixedRowCut W (τ ⋙ WordAction.functor f)
    (f.orderHom (firstColumn W (τ.obj 0) h)) hT d
  let Q' := FixedCut.changeGenerator W (generator_eq W f τ h hT) Q
  have hc := WordActionCut.cut_right W f (τ.obj d)
    (f.orderHom (firstColumn W (τ.obj 0) h)) (firstColumn W (τ.obj 0) h)
    rfl ((f.direction_eq _).trans (firstColumn_forward W (τ.obj 0) h))
    (fun k _ hk => before_firstColumn_row_mem W τ h d k hk)
    (fixedRowCut W τ (firstColumn W (τ.obj 0) h) (firstColumn_nonempty W (τ.obj 0) h) d) Q'
  exact (FixedCut.changeGenerator_right W (generator_eq W f τ h hT) Q).symm.trans hc

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
