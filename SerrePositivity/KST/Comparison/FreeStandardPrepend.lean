module

public import SerrePositivity.KST.Comparison.FreeDegeneraciesCalculations
public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.FaceDegeneracy.SimplexConeVertex

/-!
# 標準単体の自由な退化の標準形への零点の追加

概要：全射による標準形の先頭に、新しい零点を付ける。
方針：全射の先頭追加と、標準単体の頂点写像への零点の追加を組み合わせる。
規約：Segal 1974 Proposition 1.6 の模型比較。余分な退化の恒等式は別途証明する。
使われ方：標準単体の自由な退化の収縮の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite
open scoped Simplicial

/--
概要：標準単体の自由な退化の標準形の先頭に零点を追加する。
方針：全射と頂点写像の両方の始域に新しい頂点を追加する。
規約：標準形の中間次数も一つ増やす。
使われ方：余分な退化の候補の実際の写像。
-/
def freeStandardPrependNormalForm {n d : ℕ}
    (p : FatNormalForm (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋d⦌)) :
    FatNormalForm (discreteRowsFunctor.obj (Δ[n] : SSet.{u})) (op ⦋d + 1⦌) where
  degree := ⦋p.degree.len + 1⦌
  epi := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexPrepend p.epi
  epi_property := by
    let : Epi p.epi := p.epi_property
    infer_instance
  simplex := SSet.stdSimplex.objEquiv.symm
    (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.simplexConeZero (SSet.stdSimplex.objEquiv p.simplex))

/--
概要：標準単体の自由な退化に零点を追加する次数ごとの写像。
方針：各元を正規化し、標準形を拡張してから実際の模型へ戻す。
規約：自然な単体集合の射ではなく、余分な退化となる異なる次数の写像。
使われ方：標準単体の augmentation の可縮性。
-/
def freeStandardPrepend (n d : ℕ) :
    (freeDegeneracies.obj (Δ[n] : SSet.{u})).obj (op ⦋d⦌) ⟶
      (freeDegeneracies.obj (Δ[n] : SSet.{u})).obj (op ⦋d + 1⦌) :=
  ↾fun x => fatNormalFormRealize _ _
    (freeStandardPrependNormalForm (freeDegeneraciesNormalForm _ _ x))

end SerrePositivity.KST.Comparison
