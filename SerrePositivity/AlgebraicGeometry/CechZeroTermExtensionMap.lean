module

public import SerrePositivity.AlgebraicGeometry.CechZeroTermDifference

/-!
概要：零次項の直積拡張と差の余鎖写像を、元の複体・中心の加群の射に自然にする。
方針：零次は成分の直積、正次数は元の余鎖写像を使う。
規約：差の写像の自然性には、制限と中心の増大写像の可換性を明示する。
使われ方：F8 の全複体の共通細分・底変換等の比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u v
variable {R : Type v} [CommRing R]
variable {C C' C'' D D' : CochainComplex (ModuleCat.{u} R) ℕ}
variable {Q Q' Q'' : ModuleCat.{u} R}

/-- 零次項の直積拡張への射の各次数の成分。 -/
def cechZeroTermExtensionMapComponent (α : C ⟶ C') (q : Q →ₗ[R] Q') :
    ∀ n, (cechZeroTermExtension C Q).X n ⟶ (cechZeroTermExtension C' Q').X n
  | 0 => { hom' := LinearMap.prodMap (α.f 0).hom q }
  | n + 1 => α.f (n + 1)

/-- 複体と中心の項の射が誘導する、零次項の直積拡張の射。 -/
def cechZeroTermExtensionMap (α : C ⟶ C') (q : Q →ₗ[R] Q') :
    cechZeroTermExtension C Q ⟶ cechZeroTermExtension C' Q' :=
  CochainComplex.ofHom (cechZeroTermExtensionMapComponent α q) (by
    intro n
    cases n with
    | zero =>
      change cechZeroTermExtensionMapComponent α q 0 ≫ (cechZeroTermExtension C' Q').d 0 1 =
        (cechZeroTermExtension C Q).d 0 1 ≫ α.f 1
      rw [cechZeroTermExtension_d, cechZeroTermExtension_d]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact congrArg (fun m ↦ m.hom x.1) (α.comm 0 1)
    | succ n =>
      change α.f (n + 1) ≫ (cechZeroTermExtension C' Q').d (n + 1) (n + 2) =
        (cechZeroTermExtension C Q).d (n + 1) (n + 2) ≫ α.f (n + 2)
      rw [cechZeroTermExtension_d, cechZeroTermExtension_d]
      exact α.comm (n + 1) (n + 2))

/-- 零次項拡張の射は合成を保つ。 -/
theorem cechZeroTermExtensionMap_comp
    (α : C ⟶ C') (α' : C' ⟶ C'') (q : Q →ₗ[R] Q') (q' : Q' →ₗ[R] Q'') :
    cechZeroTermExtensionMap α q ≫ cechZeroTermExtensionMap α' q' =
      cechZeroTermExtensionMap (α ≫ α') (q'.comp q) := by
  ext n x
  cases n <;> rfl

/-- 零次項拡張の射は恒等を保つ。 -/
theorem cechZeroTermExtensionMap_id :
    cechZeroTermExtensionMap (𝟙 C) (LinearMap.id : Q →ₗ[R] Q) = 𝟙 _ := by
  ext n x
  cases n <;> rfl

/-- 元の複体への射影は複体と中心の項の射に自然。 -/
theorem cechZeroTermExtensionMap_projection (α : C ⟶ C') (q : Q →ₗ[R] Q') :
    cechZeroTermExtensionMap α q ≫ cechZeroTermProjection C' Q' =
      cechZeroTermProjection C Q ≫ α := by
  ext n x
  cases n <;> rfl

/-- 可換な制限と中心の増大写像は、差の余鎖写像の可換四角を与える。 -/
theorem cechZeroTermDifference_naturality
    (f : C ⟶ D) (f' : C' ⟶ D')
    (γ : Q →ₗ[R] D.X 0) (γ' : Q' →ₗ[R] D'.X 0)
    (hγ : ∀ q, (D.d 0 1).hom (γ q) = 0)
    (hγ' : ∀ q, (D'.d 0 1).hom (γ' q) = 0)
    (α : C ⟶ C') (β : D ⟶ D') (q : Q →ₗ[R] Q')
    (hsquare : f ≫ β = α ≫ f')
    (hcenter : (β.f 0).hom.comp γ = γ'.comp q) :
    cechZeroTermDifference C D f Q γ hγ ≫ β =
      cechZeroTermExtensionMap α q ≫ cechZeroTermDifference C' D' f' Q' γ' hγ' := by
  ext n x
  cases n with
  | zero =>
    change (β.f 0).hom ((f.f 0).hom x.1 - γ x.2) =
      (f'.f 0).hom ((α.f 0).hom x.1) - γ' (q x.2)
    rw [map_sub]
    exact congrArg₂ (fun a b ↦ a - b)
      (congrArg (fun m ↦ (m.f 0).hom x.1) hsquare)
      (congrArg (fun m ↦ m x.2) hcenter)
  | succ n =>
    exact congrArg (fun m ↦ (m.f (n + 1)).hom x) hsquare

end SerrePositivity.AlgebraicGeometry
