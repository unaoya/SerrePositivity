module
public import SerrePositivity.InfinityCategories.Derived.DGQuotientRoofConstantComparison
public import SerrePositivity.InfinityCategories.Derived.DGQuotientActualRelativeHomotopies

/-! # 実屋根比較の有限相対充填

概要：固定商 Hom と元の屋根 Hom の比較 span に、指定全実境界の有限相対充填を接続する。
方針：同じ元の共通実分母を屋根添字に取り、実単体と境界固定ホモトピーを自然比較で読む。
規約：余極限の比較や局所化の普遍性はまだ主張しない。使われ方：屋根比較の充填判定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
  DifferentialGraded DGQuotient DGNerve DGNerve.PinchedHom SSet
open scoped Simplicial

/-- 二つの指定実単体写像の間の、全境界上定値な実ホモトピー。 -/
structure RoofBoundaryFixedHomotopy {X : SSet.{u}} {n : ℕ} (f g : Δ[n] ⟶ X) where
  homotopy : SSet.Homotopy f g
  boundary : (∂Δ[n]).ι ▷ Δ[1] ≫ homotopy.h = fst _ _ ≫ (∂Δ[n]).ι ≫ f

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable [IsDGPretriangulated A D]

/-- 屋根比較の span は、任意の有限族の指定全実境界に共通実分母後で相対充填を持つ。 -/
theorem dgQuotientRoofFinite_relative_fillers (P : Set D) (hP : localKFlat A D P)
    {m n : ℕ} (x : D) (y : Fin m → D)
    (b : ∀ i, (∂Δ[n + 1] : SSet.{max u v}) ⟶ DGNerve.pinchedHom A D x (y i))
    (g : ∀ i, (DGNerve.pinchedHom A (QuotientObject D P)
      ((inclusion A D P).obj x) ((inclusion A D P).obj (y i))) _⦋n + 1⦌)
    (hb : ∀ i, b i ≫ pinchedHomChainMap ((inclusion A D P).map x (y i)) =
      (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (g i)) :
    ∃ s : DGClosedVerdierDenominators A D P x,
      ∃ t : ∀ i, ((dgClosedVerdierRoofDiagram A D P x (y i)).obj (op s)) _⦋n + 1⦌,
        (∀ i, (∂Δ[n + 1]).ι ≫ SSet.yonedaEquiv.symm (t i) =
          b i ≫ pinchedClosedPrecomposition A D s.obj.hom) ∧
        ∀ i, Nonempty (RoofBoundaryFixedHomotopy
          (SSet.yonedaEquiv.symm (g i) ≫
            (dgQuotientRoofConstantComparison A D P x (y i)).app (op s))
          (SSet.yonedaEquiv.symm (t i) ≫
            (dgQuotientRoofComparison A D P x (y i)).app (op s))) := by
  obtain ⟨q, s, hs, t, ht, hh⟩ :=
    dgQuotientFinite_exists_actualRelativeHomotopies A D P hP x y b g hb
  refine ⟨⟨Over.mk s, hs⟩, fun i => (t i).toPinched, ht, ?_⟩
  intro i
  let H := Classical.choice (hh i)
  change Nonempty (RoofBoundaryFixedHomotopy
    (SSet.yonedaEquiv.symm (g i) ≫ pinchedHomChainMap _)
    (SSet.yonedaEquiv.symm (t i).toPinched ≫ pinchedHomChainMap _))
  rw [pinchedLinearSimplexMap_yoneda, SSet.yonedaEquiv_symm_comp]
  exact ⟨⟨H.homotopy, H.boundary⟩⟩

end SerrePositivity.InfinityCategories
