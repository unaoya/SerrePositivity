module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.LaxCosliceDiagonalComma
public import Mathlib.CategoryTheory.Yoneda

/-!
概要：太い coslice と対角関手の固定始域 comma は単体集合として同型。
方針：任意のパラメータの族の自然な全単射に Yoneda を適用する。
規約：充填性の仮定なし。実際の自然変換を持つ comma を使う。
使われ方：標準 comma の弱可縮性と対角関手の cofinality。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：太い coslice と対角 comma の単体集合の同型。
方針：全てのパラメータの族の全単射と前合成自然性を使う。
規約：頂点だけの比較に限定しない。使われ方：comma の模型を厳密に交換する。 -/
def laxCosliceDiagonalCommaIso {K C : SSet.{u}} (p : K ⟶ C) :
    laxCoslice p ≅ unitCommaFiber (constantDiagram K C) (functorVertex p) :=
  Yoneda.ext _ _
    (fun {A} f ↦ laxCosliceDiagonalCommaHomEquiv p A f)
    (fun {A} f ↦ (laxCosliceDiagonalCommaHomEquiv p A).symm f)
    (fun f ↦ (laxCosliceDiagonalCommaHomEquiv p _).symm_apply_apply f)
    (fun f ↦ (laxCosliceDiagonalCommaHomEquiv p _).apply_symm_apply f)
    laxCosliceDiagonalCommaHomEquiv_naturality

end SerrePositivity.InfinityCategories.F2
