module

public import SerrePositivity.KST.DerivedBlowup.ChartCochainMaps
public import SerrePositivity.KST.DerivedBlowup.ExteriorMapInclusion
public import SerrePositivity.KST.DerivedBlowup.ExteriorCochainMapTransport

/-!
概要：KST §3.1 の三重重なりでの Koszul 基底変換の cochain cocycle。
方針：総外積への単射で、生成元変換の厳密 cocycle を使う。
規約：規格化座標の関数等式による複体の添字移送を明示する。
使われ方：チャート図式の複体遷移の整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {B : Type u} [CommRing B]

/-- 概要：微分の等式による複体の移送は総外積への包含を保つ。
方針：微分の等式を消去する。
規約：KST Def3.1。使われ方：座標規格化の等式に沿う cocycle の比較。 -/
theorem exteriorCochainInclusion_eqToHom {M : Type v} [AddCommGroup M] [Module B M]
    {d d' : M →ₗ[B] B} (h : d = d') (q : ℤ) (z : (exteriorKoszulCochain d).X q) :
    exteriorCochainInclusion d' q
        ((eqToHom (congrArg exteriorKoszulCochain h)).f q z) =
      exteriorCochainInclusion d q z := by
  subst d'
  rfl

variable {I : Type v} [DecidableEq I]

/-- 概要：Koszul 基底変換を整数 cochain 射として取る。
方針：線形変換と微分適合性を既存 exteriorKoszulCochainMap へ渡す。
規約：KST §3.1。使われ方：三重重なりの cocycle の成分。 -/
def chartExteriorCochainMap (a x : I → B) (i k : I) (s : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) :
    chartExteriorCochain a (normalizeCoordinates x s) k ⟶ chartExteriorCochain a x i :=
  exteriorKoszulCochainMap (koszulGeneratorMap i k x s)
    (chartKoszulDifferential a (normalizeCoordinates x s) k)
    (chartKoszulDifferential a x i) (koszulGeneratorMap_differential a x i k s hi hs)

/-- 概要：cochain のチャート遷移は三重重なりで cocycle を満たす。
方針：包含の自然性と生成元変換の厳密 cocycle を用いる。
規約：KST §3.1、二重規格化と単一規格化の等式による移送を右辺に明記。
使われ方：導来チャートの複体図式の整合性。 -/
theorem chartExteriorCochainMap_cocycle (a x : I → B) (i k l : I) (s t : Bˣ)
    (hi : x i = 1) (hs : ↑s = x k) (ht : ↑t = normalizeCoordinates x s l) :
    chartExteriorCochainMap a (normalizeCoordinates x s) k l t
        (normalizeCoordinates_pivot x k s hs) ht ≫
      chartExteriorCochainMap a x i k s hi hs =
      eqToHom (congrArg exteriorKoszulCochain
        (congrArg (fun y => chartKoszulDifferential a y l) (normalizeCoordinates_cocycle x s t))) ≫
        chartExteriorCochainMap a x i l (s * t) hi (transitionUnit_cocycle x l s t ht) := by
  have hd := congrArg (fun y => chartKoszulDifferential a y l)
    (normalizeCoordinates_cocycle x s t)
  have hsingle := koszulGeneratorMap_differential a x i l (s * t) hi
    (transitionUnit_cocycle x l s t ht)
  have hdouble := hsingle.trans hd.symm
  dsimp only [chartExteriorCochainMap]
  rw [exteriorKoszulCochainMap_comp_eq _ _ _ _ _ _ _ _ hdouble
    (koszulGeneratorMap_cocycle i k l x s t hs ht)]
  exact exteriorKoszulCochainMap_transport_source _ _ _ _ hd hdouble hsingle

end SerrePositivity.KST.DerivedBlowup
