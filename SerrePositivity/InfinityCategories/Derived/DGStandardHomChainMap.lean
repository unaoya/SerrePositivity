module
public import SerrePositivity.InfinityCategories.Derived.DGStandardSimplexMap
/-!
概要：Hom 鎖写像を標準 DK 写像空間の実単体的写像へ送る。
方針：標準座標との符号同値で pinched 線形作用を共役する。
規約：対象の Small 性を仮定せず、すべての面と退化を保つ。
使われ方：D-8 c5 の実写像空間の積の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DoldKanComparison DGNerve.PinchedHom
variable {R : Type u} [CommRing R] {D E : Type v} [DGCategory R D] [DGCategory R E]

lemma dgStandardSimplexMap_pullback {x y : D} {a b : E}
    (φ : homObject R D x y ⟶ homObject R E a b) {m n : ℕ}
    (α : Fin (m + 1) →o Fin (n + 1)) (s : StandardSimplex R x y n) :
    dgStandardSimplexMap φ (standardPullback α s) =
      standardPullback α (dgStandardSimplexMap φ s) := by
  unfold dgStandardSimplexMap standardPullback
  simp only [LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply,
    LinearMap.comp_apply]
  congr 1
  exact pinchedLinearSimplexMap_pullback φ α _

def dgStandardHomChainMap {x y : D} {a b : E}
    (φ : homObject R D x y ⟶ homObject R E a b) :
    standardHomSpace (R := R) x y ⟶ standardHomSpace (R := R) a b where
  app _ := ↾(dgStandardSimplexMap φ)
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro s
    exact dgStandardSimplexMap_pullback φ α.unop.toOrderHom s

end SerrePositivity.InfinityCategories
