module

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.HomotopyCategoryMap
public import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal

/-!
概要：単体的ホモトピーからホモトピー圏の自然変換を作る。
方針：頂点ごとの縦辺を成分とし、積の二つの三角形から自然性を示す。
規約：区間の向きは 0 から 1。quasicategory の仮定は不要。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） のホモトピー圏への移行。

対応節は Kerodon 1.4（Tag 0039）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory SSet SimplicialObject.Truncated
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories

/-- 概要：標準区間の 0 から 1 への辺。
方針：標準単体の恒等一単体を取り、端点を直接計算する。
規約：二切断の辺として扱う。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） のホモトピーの成分。 -/
def homotopyIntervalEdge : SSet.Truncated.Edge
    (X := (truncation 2).obj (Δ[1] : SSet.{u}))
    (stdSimplex.obj₀Equiv.symm 0) (stdSimplex.obj₀Equiv.symm 1) where
  edge := stdSimplex.edge 1 0 1 (by decide)
  src_eq := by apply stdSimplex.obj₀Equiv.injective; rfl
  tgt_eq := by apply stdSimplex.obj₀Equiv.injective; rfl

/-- 概要：ホモトピーの両端が誘導する関手の間の自然変換。
方針：各頂点での縦辺を取り、正方形の二つの三角形の合成関係を用いる。
規約：任意の単体集合間のホモトピーを扱う。両端は `ι₀ ≫ H` と `ι₁ ≫ H`。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） の関手間の比較。 -/
noncomputable def homotopyNatTrans {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y) :
    (hoFunctor.map (SSet.ι₀ ≫ H)).toFunctor ⟶
      (hoFunctor.map (SSet.ι₁ ≫ H)).toFunctor :=
  SSet.Truncated.HomotopyCategory.mkNatTrans
    (fun x ↦ SSet.Truncated.HomotopyCategory.homMk
      (((SSet.Truncated.Edge.id x).tensor homotopyIntervalEdge).map ((truncation 2).map H)))
    (fun {x y} e ↦ by
      have h := congrArg
        (fun k ↦ (SSet.Truncated.mapHomotopyCategory ((truncation 2).map H)).map k)
        (SSet.Truncated.HomotopyCategory.BinaryProduct.square e homotopyIntervalEdge)
      simpa only [CategoryTheory.Functor.map_comp,
        SSet.Truncated.mapHomotopyCategory_homMk] using! h)

/-- 概要：自然変換の頂点成分は、その頂点を通る区間の辺の像である。
方針：自然変換の定義を展開する。規約：頂点は二切断と元の単体集合で同一視する。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） の自然変換の具体的計算。 -/
lemma homotopyNatTrans_app {X Y : SSet.{u}} (H : X ⊗ Δ[1] ⟶ Y) (x : X _⦋0⦌) :
    (homotopyNatTrans H).app (SSet.HomotopyCategory.mk x) =
      SSet.Truncated.HomotopyCategory.homMk
        (((SSet.Truncated.Edge.id (X := (truncation 2).obj X) x).tensor
          homotopyIntervalEdge).map ((truncation 2).map H)) :=
  rfl

/-- 概要：指定された両端 `f`・`g` を持つホモトピーから自然変換を得る。
方針：両端の等式で置き換え、区間から作った自然変換を適用する。
規約：等式 `h₀`・`h₁` は両端の条件であり、quasicategory 性は不要。
使われ方：HTT §1.2.3、Kerodon §1.4.5（Tag 0049） のホモトピーの利用側 API。 -/
noncomputable def homotopyNatTransOfEndpoints {X Y : SSet.{u}} {f g : X ⟶ Y}
    (H : X ⊗ Δ[1] ⟶ Y) (h₀ : SSet.ι₀ ≫ H = f) (h₁ : SSet.ι₁ ≫ H = g) :
    (hoFunctor.map f).toFunctor ⟶ (hoFunctor.map g).toFunctor := by
  subst f g
  exact homotopyNatTrans H

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
