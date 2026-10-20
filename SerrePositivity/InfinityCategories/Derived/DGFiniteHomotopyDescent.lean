module
public import SerrePositivity.InfinityCategories.Derived.DGCoefficientFinitePairs
public import SerrePositivity.InfinityCategories.Derived.HomotopyEndpointPair
public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteProd

/-! # 有限パラメータの商 Hom ホモトピーの両端固定下降

概要：商内の指定ホモトピーを、一つの追加閉分母後に元の Hom 内へ下ろす。
方針：円柱の両端を一般有限対の指定部分とし、全体を係数充填する。
規約：商内の比較の全時刻固定を両端で保持する。使われ方：実屋根合成の有限族の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded
open DGQuotient DGNerve SSet
open scoped Simplicial
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : Set D) {K : SSet.{max u v}} (x y : D)
variable (f g : K ⟶ DGNerve.pinchedHom A D x y)
variable (H : SSet.Homotopy (f ≫ pinchedHomChainMap ((inclusion A D P).map x y))
  (g ≫ pinchedHomChainMap ((inclusion A D P).map x y)))

/-- 元の Hom 内への有限ホモトピー下降と、両端を全時刻固定する商内の比較。 -/
structure DGFiniteHomotopyDescent where
  source : D
  denominator : ForgetEnrichment.of (Complex A) source ⟶ ForgetEnrichment.of (Complex A) x
  denominator_mem : (dgClosedEdge A D denominator).edge ∈ dgVerdierEdges A D P
  homotopy : SSet.Homotopy (f ≫ pinchedClosedPrecomposition A D denominator)
    (g ≫ pinchedClosedPrecomposition A D denominator)
  comparison : SSet.Homotopy
    (H.h ≫ pinchedClosedPrecomposition A (QuotientObject D P)
      (q := (inclusion A D P).obj source) (x := (inclusion A D P).obj x)
      (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map denominator))
    (homotopy.h ≫ pinchedHomChainMap ((inclusion A D P).map source y))
  fixed : (homotopyEndpointPair K ▷ (Δ[1] : SSet.{max u v})) ≫ comparison.h =
    fst (K ⨿ K) Δ[1] ≫ homotopyEndpointPair K ≫ H.h ≫
      pinchedClosedPrecomposition A (QuotientObject D P)
        (q := (inclusion A D P).obj source) (x := (inclusion A D P).obj x)
        (y := (inclusion A D P).obj y) ((inclusion A D P).onClosed.map denominator)

/-- 商内の有限ホモトピーは、両端を固定した実比較ごと一つの追加閉分母後に下降する。 -/
theorem dgFiniteHomotopyDescent_nonempty [IsDGPretriangulated A D] [K.Finite]
    (hP : localKFlat A D P) : Nonempty (DGFiniteHomotopyDescent A D P x y f g H) := by
  let i := homotopyEndpointPair K
  have ha : coprod.desc f g ≫ pinchedHomChainMap ((inclusion A D P).map x y) = i ≫ H.h := by
    apply coprod.hom_ext
    · dsimp only [i, homotopyEndpointPair]
      rw [← Category.assoc, coprod.inl_desc, ← Category.assoc, coprod.inl_desc]
      exact H.h₀.symm
    · dsimp only [i, homotopyEndpointPair]
      rw [← Category.assoc, coprod.inr_desc, ← Category.assoc, coprod.inr_desc]
      exact H.h₁.symm
  obtain ⟨R⟩ := dgCoefficientFinitePairs_nonempty A D P i x y (coprod.desc f g) H.h hP ha
  let h : SSet.Homotopy (f ≫ pinchedClosedPrecomposition A D R.denominator)
      (g ≫ pinchedClosedPrecomposition A D R.denominator) := {
    h := R.filler
    h₀ := by
      change SSet.ι₀ ≫ R.filler = f ≫ pinchedClosedPrecomposition A D R.denominator
      have ht := congrArg (fun a => coprod.inl ≫ a) R.boundary
      simpa only [i, homotopyEndpointPair, ← Category.assoc, coprod.inl_desc] using ht
    h₁ := by
      change SSet.ι₁ ≫ R.filler = g ≫ pinchedClosedPrecomposition A D R.denominator
      have ht := congrArg (fun a => coprod.inr ≫ a) R.boundary
      simpa only [i, homotopyEndpointPair, ← Category.assoc, coprod.inr_desc] using ht
    rel := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro s
      exact False.elim s.1.property }
  exact ⟨⟨R.source, R.denominator, R.denominator_mem, h, R.comparison, R.fixed⟩⟩

end SerrePositivity.InfinityCategories
