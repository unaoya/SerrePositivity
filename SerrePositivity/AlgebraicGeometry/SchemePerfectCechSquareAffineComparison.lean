module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechSquareRefinement
public import SerrePositivity.AlgebraicGeometry.CechAugmentedSquareComparison
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCommonAffineCechCones

/-!
概要：同じスカラーの実際の四角形の完全性を、有限アフィン細分で比較する。
方針：実際の細分の射に、両空間の有限アフィン細分の cone の完全性を供給する。
規約：完全性を追加仮定にせず、逆像のアフィン性と被覆性を供給する。
使われ方：F8 を一つの整合したアフィン被覆とその逆像被覆で使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]
variable [IsAffineHom (pullback.diagonal (terminal.from Y))]
variable [IsAffineHom (pullback.diagonal (terminal.from X))]
variable (q : R →+* S) (φ : R →+* Γ(Y, ⊤)) (ψ : S →+* Γ(X, ⊤))
variable (hφ : f.appTop.hom.comp φ = ψ.comp q)
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hS : (p : S) = 0)
variable (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
variable (hX : ∀ O, (p : X.presheaf.obj O) = 0)
variable {ι κ : Type} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ四角形の全複体の完全性は、有限アフィン細分で保たれ反映される。
Stacks 30.2.6 の被覆比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem schemeStructurePerfectCechSquare_refinement_acyclic_iff
    (U : ι → Y.Opens) (V : κ → Y.Opens) (ρ : κ → ι)
    (hρ : ∀ j, V j ≤ U (ρ j))
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hcV : (⨆ j, V j) = ⊤) :
    (schemeStructurePerfectCechSquare f q φ ψ hφ p hp hR hS hY hX U).totalComplex.Acyclic ↔
      (schemeStructurePerfectCechSquare f q φ ψ hφ p hp hR hS hY hX V).totalComplex.Acyclic := by
  apply (schemeStructurePerfectCechSquare_refinement
    f q φ ψ hφ p hp hR hS hY hX U V ρ hρ).totalComplex_acyclic_iff_of_cones
  · exact schemeStructurePerfectCechRefinement_cone_acyclic
      Y p hp hY U V ρ hρ hU hV hcV
  · exact schemeStructurePerfectCechRefinement_cone_acyclic X p hp hX
      (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ V j) ρ
      (fun j ↦ ((Opens.map f.base).map (homOfLE (hρ j))).le)
      (fun i ↦ (hU i).preimage f) (fun j ↦ (hV j).preimage f)
      (f.iSup_preimage_eq_top hcV)
  · exact Function.bijective_id
  · exact Function.bijective_id

/-- 二つの有限アフィン被覆での同じ四角形の全複体の完全性は同値。
Stacks 30.2.6 の被覆比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem schemeStructurePerfectCechSquare_commonAffine_acyclic_iff
    (U : ι → Y.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hcU : (⨆ i, U i) = ⊤) (hcV : (⨆ j, V j) = ⊤) :
    (schemeStructurePerfectCechSquare f q φ ψ hφ p hp hR hS hY hX U).totalComplex.Acyclic ↔
      (schemeStructurePerfectCechSquare f q φ ψ hφ p hp hR hS hY hX V).totalComplex.Acyclic := by
  let W := schemeFiniteCommonOpenCover U V
  have hW : ∀ i, IsAffineOpen (W i) := schemeFiniteCommonOpenCover_isAffineOpen U V hU hV
  have hcW : (⨆ i, W i) = ⊤ := schemeFiniteCommonOpenCover_iSup U V hcU hcV
  exact (schemeStructurePerfectCechSquare_refinement_acyclic_iff
    f q φ ψ hφ p hp hR hS hY hX U W _
    (schemeFiniteCommonOpenCover_le_left U V) hU hW hcW).trans
      (schemeStructurePerfectCechSquare_refinement_acyclic_iff
        f q φ ψ hφ p hp hR hS hY hX V W _
        (schemeFiniteCommonOpenCover_le_right U V) hV hW hcW).symm

end SerrePositivity.AlgebraicGeometry
