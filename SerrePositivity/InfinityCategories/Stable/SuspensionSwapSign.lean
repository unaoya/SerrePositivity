module
public import SerrePositivity.InfinityCategories.Stable.SymmetricCoconeHomAddition
public import SerrePositivity.InfinityCategories.Stable.SuspensionFixedReindexSwap

/-! # 懸垂の二枝交換の負号

概要：安定 ∞ 圏の任意の懸垂四角形の二枝交換の標準自己同型は負の恒等射である。
方針：対称 span の Hom 演算と加法の一致から得る符号を、対称な懸垂模型と標準比較を通して移す。
規約：既存の懸垂と前加法構造の選択は変更しない。使われ方：三角形の回転の第三射の負号。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：等しい対象の負の恒等射は Arrow の対象として等しい。
方針：対象の等号を消す。
規約：任意の前加法圏。使われ方：余錐頂点と懸垂頂点の表示を揃える。 -/
lemma stableArrow_neg_id_congr {C : Type*} [Category* C] [Preadditive C]
    {A B : C} (h : A = B) : (Arrow.mk (-𝟙 A) : Arrow C) = Arrow.mk (-𝟙 B) := by
  subst B
  rfl

section
variable {X : SSet.{u}} [Quasicategory X] [IsStable X]
local instance : Preadditive X.HomotopyCategory := preadditive_ho (X := X)

/-- 概要：同じ二枝の span と等しい図式の余極限でも、二枝交換は負の恒等射。
方針：図式の等号を消して対称 span の符号の定理を使う。
規約：固定図式の等号と交換不変性を明示。使われ方：懸垂四角形の標準 span 表示への適用。 -/
lemma fixedCoconeSwap_eq_neg_id_of_diagram_eq {x z : X _⦋0⦌}
    (f : SSet.Truncated.Edge (X := (truncation 2).obj X) x z) (hz : IsZeroVertex z)
    {p : (horn 2 0 : SSet.{u}) ⟶ X} (h : p = edgeSpan f f)
    (c : JoinCocone p) (hc : IsColimitCone c) (hp : spanSwap ≫ p = p) :
    (fixedCoconeReindexVertexIso c hc spanSwap hp spanSwap_comp_self).hom =
      -𝟙 (SSet.HomotopyCategory.mk c.vertex : hoFunctor.obj X) := by
  subst p
  exact fixedCoconeSwap_eq_neg_id f hz c hc

/-- 概要：選んだ対称な懸垂模型の標準交換自己同型は負の恒等射。
方針：対称 span と四角形の span を同定し、余錐の交換と swapIso の Arrow の等号を使う。
規約：頂点の表示変更も明示的に扱う。使われ方：任意の懸垂の選択への符号の転送。 -/
lemma chosenSymmetricSuspensionSquare_swapIso_eq_neg_id (x : X _⦋0⦌) :
    (chosenSymmetricSuspensionSquare x).swapIso.hom =
      -𝟙 (SSet.HomotopyCategory.mk
        (chosenSymmetricSuspensionSquare x).vertex : hoFunctor.obj X) := by
  let s := chosenSymmetricSuspensionSquare x
  let f := Classical.choice ((chosenZeroVertex X).isTerminal.nonempty_edge x)
  have hs : pushoutSpan s.square = edgeSpan f f :=
    symmetricSuspensionSquare_span f (chosenZeroVertex X).isZero
  have hp := s.spanSwap_fixed (chosenSymmetricSuspensionSquare_sameSpan x)
  have hneg := fixedCoconeSwap_eq_neg_id_of_diagram_eq f (chosenZeroVertex X).isZero hs
    (pushoutCocone s.square) s.isPushout hp
  have hv : (pushoutCocone s.square).vertex = s.vertex := pushoutCocone_vertex s.square
  have hN := congrArg (fun u => (Arrow.mk u : Arrow (hoFunctor.obj X))) hneg
  have hO := stableArrow_neg_id_congr
    (congrArg (fun v => (SSet.HomotopyCategory.mk v : hoFunctor.obj X)) hv)
  apply Arrow.mk_injective
  exact (chosenSymmetricSuspensionSquare_reindex_swap_arrow x).symm.trans (hN.trans hO)

/-- 概要：任意の懸垂四角形の二枝交換の標準自己同型は負の恒等射。
方針：選んだ対称模型の符号を、懸垂の標準比較同型との可換性で任意の選択へ移す。
規約：追加の span の等号や対称な二枝の仮定は不要。使われ方：回転の第三射の符号の確定。 -/
lemma SuspensionSquare.swapIso_eq_neg_id {x : X _⦋0⦌} (s : SuspensionSquare x) :
    s.swapIso.hom = -𝟙 (SSet.HomotopyCategory.mk s.vertex : hoFunctor.obj X) :=
  s.swapIso_eq_neg_id_of_chosenSymmetric (chosenSymmetricSuspensionSquare_swapIso_eq_neg_id x)

end
end SerrePositivity.InfinityCategories
