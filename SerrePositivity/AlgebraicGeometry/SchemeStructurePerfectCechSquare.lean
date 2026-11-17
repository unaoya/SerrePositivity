module

public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquare
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechPullbackAugmentation
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechAugmentationComposition

/-!
概要：既存の四角形のデータへ、実際の構造層の Frobenius 係数と射を入れる。
方針：基底・中心・制限・増大写像を明示し、スカラーの整合性から可換性を得る。
規約：新しい全複体や完全性の仮定を追加しない。
使われ方：射影四角形の全複体を閉中心の逆像被覆で比較する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
variable {X Y : Scheme.{u}} {ι : Type} [LinearOrder ι]

set_option backward.isDefEq.respectTransparency false in
/-- 既存の増大四角形へ、実際のスカラー・制限と構造層の Frobenius 係数を入れた値。 -/
def schemeStructurePerfectCechSquare
    (f : X ⟶ Y) (q : R →+* S) (φ : R →+* Γ(Y, ⊤)) (ψ : S →+* Γ(X, ⊤))
    (hφ : f.appTop.hom.comp φ = ψ.comp q)
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)
    (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
    (hX : ∀ O, (p : X.presheaf.obj O) = 0) (U : ι → Y.Opens) :
    CechAugmentedSquare.{u} ℤ where
  C := fullCechComplex (openCoverCechDiagram (frobeniusRingDiagram Y.presheaf p hp hY) U)
  E := fullCechComplex (openCoverCechDiagram (frobeniusRingDiagram X.presheaf p hp hX)
    (fun i ↦ f ⁻¹ᵁ U i))
  restriction := schemeStructurePerfectCechPullbackMap f p hp hY hX U
  base := ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)
  centerBase := ModuleCat.of ℤ (FrobeniusDirectLimit S p hp hS)
  scalar := schemeStructurePerfectCechAugmentation Y φ p hp hR hY U
  quotient := (frobeniusDirectLimitMap p hp hR hS q).toAddMonoidHom.toIntLinearMap
  center := schemeStructurePerfectCechAugmentation X ψ p hp hS hX (fun i ↦ f ⁻¹ᵁ U i)
  scalar_cycle x := LinearMap.congr_fun
    (schemeStructurePerfectCechAugmentation_cycle Y φ p hp hR hY U) x
  center_cycle x := LinearMap.congr_fun
    (schemeStructurePerfectCechAugmentation_cycle X ψ p hp hS hX (fun i ↦ f ⁻¹ᵁ U i)) x
  commutes := (schemeStructurePerfectCechPullbackMap_augmentation
    f φ (ψ.comp q) hφ.symm p hp hR hY hX U).trans
      (schemeStructurePerfectCechAugmentation_comp X ψ q p hp hR hS hX (fun i ↦ f ⁻¹ᵁ U i))

end SerrePositivity.AlgebraicGeometry
