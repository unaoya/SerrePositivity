module

public import SerrePositivity.AlgebraicGeometry.AffineModuleCechDiagram
public import SerrePositivity.AlgebraicGeometry.ProjectiveLocalizationMapRestriction

/-!
概要：アフィン標準被覆の係数図式を加群の射に自然にする。
方針：局所化した加群写像と分母の整除による制限の可換性を使う。
規約：基底環と被覆元を固定する。
使われ方：共通細分・底変換の Čech 比較の係数の射への自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {A : Type u} [CommRing A] {ι : Type} [DecidableEq ι] (f : ι → A)
variable {M N P : Type u} [AddCommGroup M] [Module A M]
variable [AddCommGroup N] [Module A N] [AddCommGroup P] [Module A P]

/-- 加群写像が誘導する、各有限交叉の局所化加群の図式の射。 -/
def affineModuleCechMap (g : M →ₗ[A] N) :
    affineModuleCechDiagram M f ⟶ affineModuleCechDiagram N f where
  app T := ModuleCat.ofHom (IsLocalizedModule.map (Submonoid.powers (affineCechDenominator f T))
    (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) g)
  naturality {T U} h := by
    apply ModuleCat.hom_ext
    exact projectiveLocalizedModuleMap_restriction
      (affineCechDenominator_dvd f (leOfHom h)) g

/-- 局所化した係数写像は恒等写像を保つ。 -/
theorem affineModuleCechMap_id :
    affineModuleCechMap f (LinearMap.id : M →ₗ[A] M) = 𝟙 (affineModuleCechDiagram M f) := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | _ m s =>
    change IsLocalizedModule.map (Submonoid.powers (affineCechDenominator f T))
      (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ M) LinearMap.id
        (LocalizedModule.mk m s) = LocalizedModule.mk m s
    rw [IsLocalizedModule.map_LocalizedModules, LinearMap.id_apply]

/-- 局所化した係数写像は合成を保つ。 -/
theorem affineModuleCechMap_comp (g : M →ₗ[A] N) (h : N →ₗ[A] P) :
    affineModuleCechMap f g ≫ affineModuleCechMap f h = affineModuleCechMap f (h.comp g) := by
  apply NatTrans.ext
  funext T
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using LocalizedModule.induction_on with
  | _ m s =>
    change IsLocalizedModule.map (Submonoid.powers (affineCechDenominator f T))
      (LocalizedModule.mkLinearMap _ N) (LocalizedModule.mkLinearMap _ P) h
      (IsLocalizedModule.map (Submonoid.powers (affineCechDenominator f T))
        (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ N) g
        (LocalizedModule.mk m s)) =
      IsLocalizedModule.map (Submonoid.powers (affineCechDenominator f T))
        (LocalizedModule.mkLinearMap _ M) (LocalizedModule.mkLinearMap _ P) (h.comp g)
        (LocalizedModule.mk m s)
    rw [IsLocalizedModule.map_LocalizedModules, IsLocalizedModule.map_LocalizedModules,
      IsLocalizedModule.map_LocalizedModules, LinearMap.comp_apply]

end SerrePositivity.AlgebraicGeometry
