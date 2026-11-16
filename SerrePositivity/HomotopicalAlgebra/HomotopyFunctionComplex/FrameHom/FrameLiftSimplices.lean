module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLiftContraction
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# 元の持ち上げ空間の単体と実際の持ち上げ射

概要：Low 命題 3.6 の持ち上げ空間の全単体を元の可換三角形と同定する。
方針：既存の fiber の評価の引き戻し普遍性と点の単体の一意性を使う。
規約：別の fiber を定義せず、元の LiftSpace の包含を順写像に使う。
使われ方：全単体の反対要素圏と分解の comma 圏の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.SerrePositivity.HomotopyFunctionComplex

variable {C : Type u} [Category.{v} C]
  (A : SimplexCategory ⥤ C) {X E B : C}
  (a : A ⟶ (Functor.const SimplexCategory).obj X) (p : E ⟶ B) (f : X ⟶ B)

/-- 概要：元の fiber の引き戻しは全単体の評価でも引き戻し（Low 命題 3.6）。
方針：評価関手の極限保存を元の引き戻しに適用する。
規約：元の包含と射影を保持する。
使われ方：持ち上げ単体の存在と一意性。 -/
lemma evaluationPullback (n : SimplexCategoryᵒᵖ) :
    IsPullback ((LiftSpace.inclusion A a p f).app n) ((LiftSpace.projection A a p f).app n)
      (((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p).app n) ((LiftSpace.point A a f).app n) :=
  ((evaluation SimplexCategoryᵒᵖ (Type v)).obj n).map_isPullback
    (IsPullback.of_hasPullback ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) (LiftSpace.point A a f))

/-- 概要：同じ零次元標準単体の各次数の単体は一意（Low 命題 3.6）。
方針：終対象への単体作用素を頂点ごとに比較する。
規約：元の標準単体の全次数を使う。
使われ方：fiber の単体の射影の一意性。 -/
lemma pointSimplex_unique {n : SimplexCategoryᵒᵖ}
    (x y : (SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)).obj n) : x = y := by
  apply SSet.stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  change (_ : Fin 1) = _
  exact Subsingleton.elim _ _

/-- 概要：元の持ち上げ単体の包含は単射（Low 命題 3.6）。
方針：元の引き戻しの二射の共同単射性と点の一意性を使う。
規約：元の fiber の単体を同一視する。
使われ方：持ち上げ射による単体の一意性。 -/
lemma inclusion_injective (n : SimplexCategoryᵒᵖ) :
    Function.Injective ((LiftSpace.inclusion A a p f).app n) := by
  intro s t h
  exact Types.ext_of_isPullback (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.evaluationPullback A a p f n) h (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.pointSimplex_unique _ _)

/-- 概要：全単体の fiber は元の持ち上げ射と全単射（Low 命題 3.6）。
方針：同じ評価の引き戻しの存在・一意性を使う。
規約：順写像は元の包含の成分そのもの。
使われ方：分解の comma 圏との全次数の比較。 -/
def simplexEquiv (n : SimplexCategoryᵒᵖ) :
    (LiftSpace.obj A a p f).obj n ≃
      {g : A.obj n.unop ⟶ E // g ≫ p = a.app n.unop ≫ f} :=
  Equiv.ofBijective (fun s => ⟨(LiftSpace.inclusion A a p f).app n s, by
    exact congrArg (fun k : LiftSpace.obj A a p f ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj B =>
      k.app n s) (LiftSpace.over A a p f)⟩) (by
    constructor
    · intro s t h
      exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.inclusion_injective A a p f n (congrArg Subtype.val h)
    · intro g
      obtain ⟨s, hs, _⟩ := Types.exists_of_isPullback (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.evaluationPullback A a p f n) g.val
        (SSet.stdSimplex.objEquiv.symm (SimplexCategory.const n.unop (SimplexCategory.mk 0) 0))
        g.property
      exact ⟨s, Subtype.ext hs⟩)

/-- 概要：同じ全単射は全単体作用素に沿う制限を保持（Low 命題 3.6）。
方針：元の fiber の包含の自然性を使う。
規約：元の cosimplicial 分解の射をそのまま使う。
使われ方：comma 圏比較の全射への作用。 -/
lemma simplexEquiv_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (s : (LiftSpace.obj A a p f).obj n) :
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv A a p f m ((LiftSpace.obj A a p f).map θ s)).val =
      A.map θ.unop ≫ (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift.simplexEquiv A a p f n s).val := by
  change (LiftSpace.inclusion A a p f).app m ((LiftSpace.obj A a p f).map θ s) =
    A.map θ.unop ≫ (LiftSpace.inclusion A a p f).app n s
  exact ConcreteCategory.congr_hom ((LiftSpace.inclusion A a p f).naturality θ) s

end SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.FrameLift
