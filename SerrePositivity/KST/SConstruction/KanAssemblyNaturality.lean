module
public import SerrePositivity.KST.SConstruction.KanAssemblyAdjoint
public import SerrePositivity.KST.SConstruction.PointedExtensionHomotopy

/-! # Kan な随伴射の選択独立性とホモトピー自然性
概要：任意に選んだ Kan 延長同士を、実際の基点固定ホモトピーで比較する。
方針：選択独立性も自然性も、同じ射を延長する二射の比較に帰着する。
規約：Ω 条件は結論に含めない。使われ方：反復 S の段の接続の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

/-- 概要：Kan な随伴射の任意の二つの選択は基点固定ホモトピーで結ばれる。
方針：両者の置換単位への制限が元の随伴射に一致することを使う。
規約：選択を明示的に渡す。使われ方：段の接続の選択独立性。 -/
lemma kanAssemblyAdjointAt_homotopy (r : ℕ) (X : StableModel.{u})
    (v w : (kanAssemblyAdjointChoices r X) _⦋0⦌) :
    ∃ H : SSet.Homotopy (kanAssemblyAdjointAt r X v).right (kanAssemblyAdjointAt r X w).right,
      ((oneDirectionKanRealizationFunctor r).obj X).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          ((loopBoundaryKanFunctor (r + 1)).obj X).hom :=
  pointedExtensions_homotopy _ (Spectra.PointedKanReplacement.unit_anodyne _)
    ((kanTargetAssemblyAdjointNat r).app X) _ _
    (kanAssemblyAdjointAt_fac r X v) (kanAssemblyAdjointAt_fac r X w)

/-- 概要：独立に選んだ Kan な随伴射は入力の射に対してホモトピー自然。
方針：単位の自然性と未延長の随伴射の自然性から、両経路の制限を一致させる。
規約：実際の基点固定ホモトピーを与える。使われ方：K の関手性への接続。 -/
lemma kanAssemblyAdjointAt_naturality_homotopy (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (v : (kanAssemblyAdjointChoices r X) _⦋0⦌)
    (w : (kanAssemblyAdjointChoices r Y) _⦋0⦌) :
    ∃ H : SSet.Homotopy
      ((oneDirectionKanRealizationFunctor r).map f ≫ kanAssemblyAdjointAt r Y w).right
      (kanAssemblyAdjointAt r X v ≫ (loopBoundaryKanFunctor (r + 1)).map f).right,
      ((oneDirectionKanRealizationFunctor r).obj X).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫
          ((loopBoundaryKanFunctor (r + 1)).obj Y).hom := by
  apply pointedExtensions_homotopy
    (Spectra.PointedKanReplacement.unit.app (oneDirectionReducedRealization r X))
    (Spectra.PointedKanReplacement.unit_anodyne _)
    ((oneDirectionReducedRealizationFunctor r).map f ≫ (kanTargetAssemblyAdjointNat r).app Y)
  · have hu := Spectra.PointedKanReplacement.unit.naturality
      ((oneDirectionReducedRealizationFunctor r).map f)
    change (oneDirectionReducedRealizationFunctor r).map f ≫
        Spectra.PointedKanReplacement.unit.app (oneDirectionReducedRealization r Y) =
      Spectra.PointedKanReplacement.unit.app (oneDirectionReducedRealization r X) ≫
        (oneDirectionKanRealizationFunctor r).map f at hu
    rw [← Category.assoc, ← hu, Category.assoc, kanAssemblyAdjointAt_fac]
  · rw [← Category.assoc, kanAssemblyAdjointAt_fac]
    exact ((kanTargetAssemblyAdjointNat r).naturality f).symm

end SerrePositivity.KST.SConstruction
