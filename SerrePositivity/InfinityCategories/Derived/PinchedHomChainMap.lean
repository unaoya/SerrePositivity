module
public import SerrePositivity.InfinityCategories.Derived.PinchedLinearChainMap

/-! # Hom 複体の鎖写像による実際の pinched 写像空間の射

概要：線形単体の写像を実際の pinched Hom へ移す。
方針：全次数の線形表示と引き戻しとの可換性で単体的自然性を証明する。
規約：対象の宇宙は共通。使われ方：β3 の写像空間の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial
variable {A : Type u} [CommRing A] {D E : Type v}
variable [DGCategory A D] [DGCategory A E] {x y : D} {x' y' : E}

/-- 鎖写像で成分を写し、実際の pinched 単体へ再構成する。 -/
def pinchedHomChainMapSimplex (φ : homObject A D x y ⟶ homObject A E x' y')
    {n : ℕ} (s : (DGNerve.pinchedHom A D x y) _⦋n⦌) :
    (DGNerve.pinchedHom A E x' y') _⦋n⦌ :=
  (pinchedLinearSimplexMap φ (toLinearSimplex s)).toPinched

/-- 実際の写像の線形表示は成分への鎖写像の適用に一致。 -/
lemma pinchedHomChainMapSimplex_linear (φ : homObject A D x y ⟶ homObject A E x' y')
    {n : ℕ} (s : (DGNerve.pinchedHom A D x y) _⦋n⦌) :
    toLinearSimplex (pinchedHomChainMapSimplex φ s) =
      pinchedLinearSimplexMap φ (toLinearSimplex s) :=
  LinearSimplex.toLinearSimplex_toPinched _

/-- 固定 Hom 複体の鎖写像が誘導する pinched Hom の単体的写像。 -/
def pinchedHomChainMap (φ : homObject A D x y ⟶ homObject A E x' y') :
    DGNerve.pinchedHom A D x y ⟶ DGNerve.pinchedHom A E x' y' where
  app _ := ↾(pinchedHomChainMapSimplex φ)
  naturality {m n} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply (linearEquiv x' y' n.unop.len).injective
    change toLinearSimplex (pinchedHomChainMapSimplex φ (s.pullback α.unop)) =
      toLinearSimplex ((pinchedHomChainMapSimplex φ s).pullback α.unop)
    rw [pinchedHomChainMapSimplex_linear, toLinearSimplex_pullback,
      toLinearSimplex_pullback, pinchedHomChainMapSimplex_linear,
      pinchedLinearSimplexMap_pullback]

end SerrePositivity.InfinityCategories
