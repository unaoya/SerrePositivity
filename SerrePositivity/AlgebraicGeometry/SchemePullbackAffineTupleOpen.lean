module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
概要：アフィン基底上の二つのアフィン開の同じファイバー積はアフィン開。
方針：制限した二つのアフィンの実際の pullback の開埋め込みの像を取る。
規約：元の射がアフィンであるとは仮定しない。
使われ方：一つの被覆から作る Čech nerve のタプル被覆のアフィン性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
variable {X Y S : Scheme.{u}} [IsAffine S]

set_option backward.isDefEq.respectTransparency false in
/-- 二つのアフィン開の、アフィン基底上の同じ pullback の開はアフィン。 -/
theorem pullbackAffineOpen_inf (f : X ⟶ S) (g : Y ⟶ S)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (pullback.fst f g ⁻¹ᵁ U ⊓ pullback.snd f g ⁻¹ᵁ V) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine V.toScheme := hV
  let k := pullback.map (U.ι ≫ f) (V.ι ≫ g) f g U.ι V.ι (𝟙 S) (by simp) (by simp)
  have : IsOpenImmersion k := by dsimp only [k]; infer_instance
  have ha : IsAffineOpen k.opensRange := isAffineOpen_opensRange k
  convert ha using 1
  apply Opens.ext
  simp only [TopologicalSpace.Opens.coe_inf, Scheme.Hom.coe_preimage, Scheme.Hom.coe_opensRange]
  simpa [k] using (Scheme.Pullback.range_map (f := U.ι ≫ f) (g := V.ι ≫ g) f g
    U.ι V.ι (𝟙 S) (by simp) (by simp)).symm

set_option backward.isDefEq.respectTransparency false in
/-- 同じ二つの開のアフィン性を、任意の実際の Cartesian square に移す。 -/
theorem isPullbackAffineOpen_inf {P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ S} {g : Y ⟶ S} (H : IsPullback a b f g)
    {U : X.Opens} {V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (a ⁻¹ᵁ U ⊓ b ⁻¹ᵁ V) := by
  have hh := (pullbackAffineOpen_inf f g hU hV).preimage H.isoPullback.hom
  simpa only [Scheme.Hom.preimage_inf, ← Scheme.Hom.comp_preimage,
    H.isoPullback_hom_fst, H.isoPullback_hom_snd] using hh

end SerrePositivity.AlgebraicGeometry
