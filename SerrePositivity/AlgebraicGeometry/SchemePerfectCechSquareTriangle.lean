module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechPullbackComposition
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechRefinedAugmentation
public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechSquare
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareMap

/-!
概要：同じ閉中心を保つ実際のスキームの三角形で、native な四角形を移す。
方針：基底側は実際の refinedPullback、中心側は同じ空間の実際の細分を使う。
規約：基底・中心の係数とスカラーを保ち、完全性を追加仮定にしない。
使われ方：Proj の表示の同型から実際のブローアップへの移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry
universe u
variable {X Y Z : Scheme.{u}} {ι : Type} [LinearOrder ι]

/-- 可換な三角形と被覆の包含は、同じ閉中心の逆像被覆の細分を与える。 -/
theorem schemePerfectCechTriangle_preimage_le
    (v : Y ⟶ Z) (f : X ⟶ Y) (g : X ⟶ Z) (he : f ≫ v = g)
    (U : ι → Z.Opens) (V : ι → Y.Opens) (hV : ∀ i, V i ≤ v ⁻¹ᵁ U i) :
    ∀ i, f ⁻¹ᵁ V i ≤ g ⁻¹ᵁ U i := by
  intro i
  rw [← he, Scheme.Hom.comp_preimage]
  exact ((Opens.map f.base).map (homOfLE (hV i))).le

variable {R S : Type u} [CommRing R] [CommRing S]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ閉中心を保つ三角形に沿う、実際の余鎖写像を持つ四角形の射。 -/
def schemeStructurePerfectCechSquare_triangleMap
    (v : Y ⟶ Z) (f : X ⟶ Y) (g : X ⟶ Z) (he : f ≫ v = g)
    (q : R →+* S) (φZ : R →+* Γ(Z, ⊤)) (φY : R →+* Γ(Y, ⊤))
    (ψ : S →+* Γ(X, ⊤)) (hφY : φY = v.appTop.hom.comp φZ)
    (hcommZ : g.appTop.hom.comp φZ = ψ.comp q)
    (hcommY : f.appTop.hom.comp φY = ψ.comp q)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)
    (hZ : ∀ O, (p : Z.presheaf.obj O) = 0)
    (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
    (hX : ∀ O, (p : X.presheaf.obj O) = 0)
    (U : ι → Z.Opens) (V : ι → Y.Opens) (hV : ∀ i, V i ≤ v ⁻¹ᵁ U i) :
    CechAugmentedSquare.Map
      (schemeStructurePerfectCechSquare g q φZ ψ hcommZ p hp hR hS hZ hX U)
      (schemeStructurePerfectCechSquare f q φY ψ hcommY p hp hR hS hY hX V) where
  left := schemeStructurePerfectCechRefinedPullbackMap v p hp hZ hY U V id hV
  right := openCoverCechRefinementMap (frobeniusRingDiagram X.presheaf p hp hX)
    (fun i ↦ g ⁻¹ᵁ U i) (fun i ↦ f ⁻¹ᵁ V i) id
    (schemePerfectCechTriangle_preimage_le v f g he U V hV)
  base := LinearMap.id
  center := LinearMap.id
  restriction := by
    change schemeStructurePerfectCechRefinedPullbackMap g p hp hZ hX U
      (fun i ↦ f ⁻¹ᵁ V i) id (schemePerfectCechTriangle_preimage_le v f g he U V hV) =
        schemeStructurePerfectCechRefinedPullbackMap v p hp hZ hY U V id hV ≫
          schemeStructurePerfectCechPullbackMap f p hp hY hX V
    rw [schemeStructurePerfectCechPullbackMap_eq_refined f p hp hY hX V]
    exact (schemeStructurePerfectCechRefinedPullbackMap_comp v f g he p hp hZ hY hX
      U V (fun i ↦ f ⁻¹ᵁ V i) hV (fun _ ↦ le_rfl)
      (schemePerfectCechTriangle_preimage_le v f g he U V hV)).symm
  scalar := by
    simpa only [schemeStructurePerfectCechSquare, LinearMap.comp_id] using
      schemeStructurePerfectCechRefinedPullbackMap_augmentation v φZ φY hφY
        p hp hR hZ hY U V id hV
  quotient := by simp [schemeStructurePerfectCechSquare]
  center_naturality := by
    simpa only [schemeStructurePerfectCechSquare, LinearMap.comp_id] using
      schemeStructurePerfectCechAugmentation_refinement X ψ p hp hS hX
        (fun i ↦ g ⁻¹ᵁ U i) (fun i ↦ f ⁻¹ᵁ V i) id
        (schemePerfectCechTriangle_preimage_le v f g he U V hV)

end SerrePositivity.AlgebraicGeometry
