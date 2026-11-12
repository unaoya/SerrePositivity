module

public import SerrePositivity.AlgebraicGeometry.SchemeStructureCech
public import SerrePositivity.AlgebraicGeometry.SchemeCechPreimage

/-!
概要：構造層の実際の引き戻しを、固定した基底環上の Čech の射にする。
方針：切断の引き戻しの自然性でスカラー作用を照合する。
規約：スカラー環の二つの写像の整合性を明示し、非平坦な射も扱う。
使われ方：閉厚化と模型の遷移の比較を、実際のスキームの射に自然にする。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace Opposite _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} {R : Type u} [CommRing R]
variable (f : X ⟶ Y) (φY : R →+* Γ(Y, ⊤)) (φX : R →+* Γ(X, ⊤))
variable (hφ : φX = f.appTop.hom.comp φY)

include hφ in
/-- 構造層の切断の引き戻しは、大域スカラーの引き戻しと整合する。 -/
theorem schemeStructureCechPullback_scalar (U : Y.Opens) (r : R) :
    (f.app U).hom ((Y.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom (φY r)) =
      (X.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ ⊤ from le_top)).op).hom (φX r) := by
  subst φX
  exact congrArg (fun g : Γ(Y, ⊤) ⟶ Γ(X, f ⁻¹ᵁ U) ↦ g.hom (φY r))
    (f.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)

include hφ in
/-- 実際の構造層の引き戻しを、固定した基底環上の前層の射として扱う。 -/
def schemeStructureCechPullbackCoefficient :
    schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars φY ⟶
      (Opens.map f.base).op ⋙
        (schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars φX) where
  app U := ModuleCat.ofHom
    (X := (schemeStructureCechPresheaf Y ⋙ ModuleCat.restrictScalars φY).obj U)
    (Y := (schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars φX).obj
      ((Opens.map f.base).op.obj U))
    { toFun := (f.app U.unop).hom
      map_add' := (f.app U.unop).hom.map_add
      map_smul' := by
        intro r x
        change (f.app U.unop).hom
          (@HMul.hMul Γ(Y, U.unop) Γ(Y, U.unop) Γ(Y, U.unop) inferInstance
            ((Y.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op).hom (φY r)) x) =
          @HMul.hMul Γ(X, f ⁻¹ᵁ U.unop) Γ(X, f ⁻¹ᵁ U.unop) Γ(X, f ⁻¹ᵁ U.unop) inferInstance
            ((X.presheaf.map (homOfLE (show f ⁻¹ᵁ U.unop ≤ ⊤ from le_top)).op).hom (φX r))
            ((f.app U.unop).hom x)
        rw [map_mul, schemeStructureCechPullback_scalar f φY φX hφ U.unop r] }
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun g : Γ(Y, U.unop) ⟶ Γ(X, f ⁻¹ᵁ V.unop) ↦ g.hom x)
      (f.naturality i)

variable {ι : Type} [DecidableEq ι]

/-- スキームの射の、構造層の Čech 複体上の実際の引き戻し。 -/
def schemeStructureCechPullbackMap (U : ι → Y.Opens) :=
  schemeCechPullbackMap f (schemeStructureCechPresheaf X ⋙ ModuleCat.restrictScalars φX)
    (schemeStructureCechPullbackCoefficient f φY φX hφ) U

end SerrePositivity.AlgebraicGeometry
