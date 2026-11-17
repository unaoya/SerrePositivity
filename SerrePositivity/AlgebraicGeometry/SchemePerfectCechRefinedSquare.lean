module

public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechSquare
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechRefinedAugmentation
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechSquareIsoComparison

/-!
概要：既存の四角形へ、中心の同じ細分した被覆と実際の引き戻しを渡す。
方針：既存の増大写像の自然性で辺を保ち、等しい被覆の同型で完全性を移す。
規約：元の基底・中心・商の写像と切断の写像を保持する。
使われ方：同じ中心のタプル被覆へ F8 の完全性を渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S] {X Y : Scheme.{u}}
variable {ι κ : Type} [LinearOrder ι] [LinearOrder κ]
variable (f : X ⟶ Y) (q : R →+* S) (φ : R →+* Γ(Y, ⊤)) (ψ : S →+* Γ(X, ⊤))
variable (hφ : f.appTop.hom.comp φ = ψ.comp q)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)
variable (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
variable (hX : ∀ O, (p : X.presheaf.obj O) = 0)

set_option backward.isDefEq.respectTransparency false in
/-- 中心の同じ細分した被覆を、既存の増大四角形へ渡した値。 -/
def schemeStructurePerfectCechRefinedSquare (U : ι → Y.Opens) (V : κ → X.Opens)
    (ρ : κ → ι) (hρ : ∀ j, V j ≤ f ⁻¹ᵁ U (ρ j)) : CechAugmentedSquare.{u} ℤ where
  C := fullCechComplex (openCoverCechDiagram (frobeniusRingDiagram Y.presheaf p hp hY) U)
  E := fullCechComplex (openCoverCechDiagram (frobeniusRingDiagram X.presheaf p hp hX) V)
  restriction := schemeStructurePerfectCechRefinedPullbackMap f p hp hY hX U V ρ hρ
  base := ModuleCat.of ℤ (FrobeniusDirectLimit R p hp hR)
  centerBase := ModuleCat.of ℤ (FrobeniusDirectLimit S p hp hS)
  scalar := schemeStructurePerfectCechAugmentation Y φ p hp hR hY U
  quotient := (frobeniusDirectLimitMap p hp hR hS q).toAddMonoidHom.toIntLinearMap
  center := schemeStructurePerfectCechAugmentation X ψ p hp hS hX V
  scalar_cycle x := LinearMap.congr_fun
    (schemeStructurePerfectCechAugmentation_cycle Y φ p hp hR hY U) x
  center_cycle x := LinearMap.congr_fun
    (schemeStructurePerfectCechAugmentation_cycle X ψ p hp hS hX V) x
  commutes := (schemeStructurePerfectCechRefinedPullbackMap_augmentation
    f φ (ψ.comp q) hφ.symm p hp hR hY hX U V ρ hρ).trans
      (schemeStructurePerfectCechAugmentation_comp X ψ q p hp hR hS hX V)

set_option backward.isDefEq.respectTransparency false in
/-- 元の逆像被覆から中心の細分へ、全ての辺を保つ実際の四角形の射。 -/
def schemeStructurePerfectCechRefinedSquare_map (U : ι → Y.Opens) (V : κ → X.Opens)
    (ρ : κ → ι) (hρ : ∀ j, V j ≤ f ⁻¹ᵁ U (ρ j)) :
    CechAugmentedSquare.Map (schemeStructurePerfectCechSquare f q φ ψ hφ p hp hR hS hY hX U)
      (schemeStructurePerfectCechRefinedSquare f q φ ψ hφ p hp hR hS hY hX U V ρ hρ) where
  left := 𝟙 _
  right := openCoverCechRefinementMap (frobeniusRingDiagram X.presheaf p hp hX)
    (fun i ↦ f ⁻¹ᵁ U i) V ρ hρ
  base := LinearMap.id
  center := LinearMap.id
  restriction := by
    change schemeStructurePerfectCechPullbackMap f p hp hY hX U ≫
      openCoverCechRefinementMap (frobeniusRingDiagram X.presheaf p hp hX)
        (fun i ↦ f ⁻¹ᵁ U i) V ρ hρ = 𝟙 _ ≫
          schemeStructurePerfectCechRefinedPullbackMap f p hp hY hX U V ρ hρ
    simp only [Category.id_comp, schemeStructurePerfectCechRefinedPullbackMap]
  scalar := by simp [schemeStructurePerfectCechSquare, schemeStructurePerfectCechRefinedSquare]
  quotient := by simp [schemeStructurePerfectCechSquare, schemeStructurePerfectCechRefinedSquare]
  center_naturality := by
    simpa only [schemeStructurePerfectCechSquare, schemeStructurePerfectCechRefinedSquare,
      LinearMap.comp_id] using
      schemeStructurePerfectCechAugmentation_refinement X ψ p hp hS hX
        (fun i ↦ f ⁻¹ᵁ U i) V ρ hρ

set_option backward.isDefEq.respectTransparency false in
/-- 同じ中心の等しい被覆への細分で、全複体の完全性は同値。
BST13 Lemma 3.9・BS17 Lemma 4.6(i) に使う Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem schemeStructurePerfectCechRefinedSquare_acyclic_iff_of_eq
    (U : ι → Y.Opens) (V : ι → X.Opens) (hV : ∀ i, V i ≤ f ⁻¹ᵁ U i)
    (he : V = fun i ↦ f ⁻¹ᵁ U i) :
    (schemeStructurePerfectCechSquare f q φ ψ hφ p hp hR hS hY hX U).totalComplex.Acyclic ↔
      (schemeStructurePerfectCechRefinedSquare f q φ ψ hφ p hp hR hS hY hX
        U V id hV).totalComplex.Acyclic := by
  let m := schemeStructurePerfectCechRefinedSquare_map f q φ ψ hφ p hp hR hS hY hX U V id hV
  have hl : IsIso m.left := by
    change IsIso (𝟙 (schemeStructurePerfectCechSquare f q φ ψ hφ p hp hR hS hY hX U).C)
    infer_instance
  have hr : IsIso m.right := by
    change IsIso (openCoverCechRefinementMap (frobeniusRingDiagram X.presheaf p hp hX)
      (fun i ↦ f ⁻¹ᵁ U i) V id hV)
    exact openCoverCechRefinementMap_isIso_of_eq _ _ _ he hV
  apply m.totalComplex_acyclic_iff_of_cones
  · apply cechRefinementCone_acyclic_of_quasiIso
    intro k
    infer_instance
  · apply cechRefinementCone_acyclic_of_quasiIso
    intro k
    infer_instance
  · exact Function.bijective_id
  · exact Function.bijective_id

end SerrePositivity.AlgebraicGeometry
