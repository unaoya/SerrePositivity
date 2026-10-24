module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoproductFunctorIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointFunctorIso
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FilteredDiagonalCofinality
public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalOpposite

/-!
概要：filtered な底の実際の二項積への対角射は right cofinal。
方針：二点の直和上の定値図式を、内部 Hom の積同型と点の関手同型で移す。
規約：hom は二つの恒等射の組そのもの。
使われ方：fiber ごとの積の全空間から二つの全空間の積への比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：filtered ∞ 圏からその二項積への対角関手は right cofinal。
方針：二点上の定値図式の cofinality を厳密な積表示で輸送する。
規約：一般の filtered ∞ 圏。使われ方：積比較の全空間による弱同値判定。 -/
lemma isRightCofinal_binaryDiagonal (B : SSet.{u}) [Quasicategory B]
    [IsFilteredInfinity B] : IsRightCofinal (lift (𝟙 B) (𝟙 B)) := by
  let e := coproductFunctorIso (Δ[0] : SSet.{u}) (Δ[0] : SSet.{u}) B
  let d := (pointFunctorIso B).symm ⊗ᵢ (pointFunctorIso B).symm
  have h := (isRightCofinal_constantDiagram_of_filtered
    ((Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u})) B).comp
      ((isRightCofinal_of_isIso e.hom).comp (isRightCofinal_of_isIso d.hom))
  have he : constantDiagram ((Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u})) B ≫
      e.hom ≫ d.hom = lift (𝟙 B) (𝟙 B) := by
    rw [← Category.assoc, constantDiagram_coproductFunctorIso]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [d, tensorIso_hom, lift_fst]
      exact (pointFunctorIso B).hom_inv_id
    · simp only [d, tensorIso_hom, lift_snd]
      exact (pointFunctorIso B).hom_inv_id
  rw [he] at h
  exact h

end SerrePositivity.InfinityCategories.F2
