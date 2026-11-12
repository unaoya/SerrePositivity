module

public import SerrePositivity.AlgebraicGeometry.AffineCechHomologyVanishing
public import SerrePositivity.AlgebraicGeometry.SchemeStructureCechNativeTensor

/-!
概要：アフィンになる flat 底変換で、元の構造層 Čech H のテンソル積が消える。
方針：実際の底変換との比較を、アフィン被覆の正次数消滅に合成する。
規約：底変換の正方形と被覆の条件を明示する。
使われ方：中心外の局所化での消滅から台の包含へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {X Y : Scheme.{u}} [IsAffine Y]
variable [IsAffineHom (pullback.diagonal (terminal.from X))]
variable (iX : X ⟶ Spec (CommRingCat.of R)) (iY : Y ⟶ Spec (CommRingCat.of A))
variable (g : Y ⟶ X)
variable (H : IsPullback g iY iX (Spec.map (CommRingCat.ofHom (algebraMap R A))))
variable {ι : Type} [LinearOrder ι] [Fintype ι] (U : ι → X.Opens)

include H in
/-- アフィンな平坦底変換で正次数の構造層 Čech H のスカラー拡大は消える。
BST13 Lemma 3.9 の台の議論に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem affineBaseChangeCechHomology_isZero
    (hflat : (algebraMap R A).Flat) (hU : ∀ i, IsAffineOpen (U i))
    (hV : ∀ i, IsAffineOpen (g ⁻¹ᵁ U i)) (hcV : (⨆ i, g ⁻¹ᵁ U i) = ⊤)
    (q : ℕ) (hq : 0 < q) :
    IsZero ((ModuleCat.extendScalars (algebraMap R A)).obj
      ((fullCechComplex (openCoverCechDiagram (schemeStructureCechPresheaf X ⋙
        ModuleCat.restrictScalars (schemeScalarHom X iX)) U)).homology q)) := by
  have hz := affineSchemeCechHomology_isZero (schemeScalarHom Y iY)
    (schemeStructureModule Y) (fun i ↦ g ⁻¹ᵁ U i) hV hcV q hq
  exact hz.of_iso (schemeStructureCechNativeFlatBaseChangeIso iX iY g H U hU hflat q)

end SerrePositivity.AlgebraicGeometry
