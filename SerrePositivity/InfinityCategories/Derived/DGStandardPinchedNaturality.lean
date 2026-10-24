module
public import SerrePositivity.InfinityCategories.Derived.DGStandardEnrichedFunctor
public import SerrePositivity.InfinityCategories.Derived.PinchedHomChainMap
public import SerrePositivity.InfinityCategories.DoldKanComparison.CoherentPinchedStandard
/-!
概要：標準 DK Hom と実 pinched Hom の同型は Hom 鎖写像に自然である。
方針：線形表示の成分と符号同値の計算で、同型の逆への作用を比較する。
規約：Small 仮定なしに全次数の係数を保持する。
使われ方：coherent 合成 prism の二入力を元の実 Hom へ照合する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom DoldKanComparison
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v} [DGCategory A D] [DGCategory A E]

lemma dgStandardPinchedIso_inv_naturality {x y : D} {x' y' : E}
    (φ : homObject A D x y ⟶ homObject A E x' y') {n : ℕ}
    (f : (DGNerve.pinchedHom A D x y) _⦋n⦌) :
    ((standardHomPinchedIso (R := A) x' y').inv.app _
      ((pinchedHomChainMap φ).app _ f)).down =
      dgStandardSimplexMap φ (((standardHomPinchedIso (R := A) x y).inv.app _ f).down) := by
  change standardSimplexEquiv x' y' n
    (toLinearSimplex (pinchedHomChainMapSimplex φ f)) = _
  rw [pinchedHomChainMapSimplex_linear]
  change standardSimplexEquiv x' y' n (pinchedLinearSimplexMap φ (toLinearSimplex f)) =
    standardSimplexEquiv x' y' n (pinchedLinearSimplexMap φ
      ((standardSimplexEquiv x y n).symm (standardSimplexEquiv x y n (toLinearSimplex f))))
  rw [LinearEquiv.symm_apply_apply]
end SerrePositivity.InfinityCategories
