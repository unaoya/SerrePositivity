module
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCompositionPrismRecovery
public import SerrePositivity.InfinityCategories.Derived.Gluing.RelativePrismEdgeClass
/-! # 明示係数 prism と指定対角辺の正本端点での相対比較

概要：明示 augmentation prism を、正本端点のまま指定係数対角変形へ両端固定で移す。
方針：既存の pinched 相対正規化を同じ区間比較で写し、指定変形の全 prism 表示を使う。
規約：元 Hom 入力・全時間・両端の全時間固定を保持する。
使われ方：六片から得る係数対角の辺の類を、指定係数対角辺へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D) (X Y : DGGluingObject R C D M)
local notation "K" => dgGluingModelUnitCollarParameter R C D M X Y

def dgGluingHomDerivedCanonicalAugmentationIntervalPrism :=
  dgGluingHomDerivedAugmentationPrism R C D M X Y ≫ pinchedHomToIntervalMappingSpace _ _

lemma dgGluingHomDerivedCanonicalAugmentationNormalization_exists :
    ∃ H : SSet.Homotopy (dgGluingHomDerivedCanonicalAugmentationIntervalPrism R C D M X Y)
        ((β_ (Δ[1] : SSet.{max (u + 1) v w}) K).hom ≫
          (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h),
      (((boundary 1).ι ▷ K) ▷ (Δ[1] : SSet.{max (u + 1) v w})) ≫ H.h =
        fst ((boundary 1 : SSet.{max (u + 1) v w}) ⊗ K) Δ[1] ≫ ((boundary 1).ι ▷ K) ≫
          (β_ (Δ[1] : SSet.{max (u + 1) v w}) K).hom ≫
            (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h := by
  obtain ⟨H, hH⟩ := dgGluingHomDerivedAugmentationNormalization_exists R C D M X Y
  let q := pinchedHomToIntervalMappingSpace
    ((dgGluingUniverseDerivedYoneda.{u, v, w} R C).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex X.left)))
    ((dgGluingUniverseDerivedCoefficient R C D M).app (Opposite.op ⦋0⦌)
      (ULift.up (Simplex.vertex Y.right)))
  let T := functorHomotopyPostcomp H q
  have hG : uncurry (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) ≫ q =
      (β_ (Δ[1] : SSet.{max (u + 1) v w}) K).hom ≫
        (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y).h := by
    rw [dgGluingHomDerivedCompositionDiagonalHomotopy_canonical_prism R C D M X Y]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    rfl
  let U := stableHomotopyRetarget T rfl hG
  refine ⟨U, ?_⟩
  have hU : U.h = H.h ≫ q := rfl
  rw [hU]
  calc
    _ = fst ((boundary 1 : SSet.{max (u + 1) v w}) ⊗ K) Δ[1] ≫
        ((boundary 1).ι ▷ K) ≫
          (uncurry (dgGluingDerivedHomCoefficientIntervalPath R C D M X Y) ≫ q) := by
      have he := congrArg (fun f => f ≫ q) hH
      simpa only [dgGluingModelUnitCollarParameter, Category.assoc] using he
    _ = _ := by rw [hG]

def dgGluingHomDerivedAugmentationDiagonalHomotopy :=
  dgGluingHomotopyOfRelativePrism (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y)
    (Classical.choose (dgGluingHomDerivedCanonicalAugmentationNormalization_exists R C D M X Y))
    (Classical.choose_spec
      (dgGluingHomDerivedCanonicalAugmentationNormalization_exists R C D M X Y))

lemma dgGluingHomDerivedAugmentationDiagonalHomotopy_h :
    (dgGluingHomDerivedAugmentationDiagonalHomotopy R C D M X Y).h =
      (β_ K (Δ[1] : SSet.{max (u + 1) v w})).hom ≫
        dgGluingHomDerivedCanonicalAugmentationIntervalPrism R C D M X Y := rfl

lemma dgGluingHomDerivedAugmentationDiagonalHomotopy_class :
    SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomDerivedAugmentationDiagonalHomotopy R C D M X Y)) =
      SSet.Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
        (dgGluingHomDerivedCompositionDiagonalHomotopy R C D M X Y)) :=
  dgGluingHomotopyOfRelativePrism_homMk_eq _ _ _
end SerrePositivity.InfinityCategories
