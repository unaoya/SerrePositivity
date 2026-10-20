module

public import SerrePositivity.InfinityCategories.HomotopyLimits.InitialEdgeFamilyRetraction

/-!
概要：初期 Hom の相対辺比較の底を、元の底の切断比較の同じ円柱へ同定する。
方針：固定終点の包含後に同じ raw な始点制限を照合する。
規約：底の代表を選び直さない。使われ方：付加辺面と native な前合成比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {E B T : SSet.{u}} [Quasicategory B] (q : E ⟶ B) [InnerFibration q]
  (c : E _⦋0⦌) (e : (Δ[1] : SSet.{u}) ⟶ E)
  (he : stdSimplex.δ (1 : Fin 2) ≫ e = SSet.yonedaEquiv.symm c)
  (y : B _⦋0⦌) (a : T ⟶ sliceUnder e)
  (ha : (a ≫ sliceUnderProjection e) ≫ q = SSet.const y)
local notation "hs" => Eq.trans (Eq.symm (Category.assoc (stdSimplex.δ (1 : Fin 2)) e q))
  (congrArg (· ≫ q) he)
local notation "I" => initialEdgeFamilyRetraction q c e he y a ha
local notation "F" => relativeEdgeFamilyBase e q a y ha

/-- 比較の底は、元の底の全辺族の同じ切断比較を始点へ制限した円柱である。 -/
lemma initialEdgeFamilyRetraction_baseCylinder :
    (I).h ≫ leftFibrationInitialProjection q c y =
      (cosliceEdgeFamilyPrecompositionCylinder (e ≫ q) y F
        (SSet.yonedaEquiv.symm c ≫ q) (stdSimplex.δ (0 : Fin 2) ≫ (e ≫ q))
        hs rfl).h := by
  apply vertexFiber_hom_ext (sliceUnderProjection (SSet.yonedaEquiv.symm c ≫ q)) y
  rw [Category.assoc, initialEdgeFamilyRetraction_base,
    cosliceEdgeFamilyPrecompositionCylinder_projection]
  simp only [Category.assoc, normalizedCoconeRestrictionFiber, vertexFiberMap_ι]

end
end SerrePositivity.InfinityCategories.HomotopyLimits
