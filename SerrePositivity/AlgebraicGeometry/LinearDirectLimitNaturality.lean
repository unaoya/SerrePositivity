module

public import SerrePositivity.AlgebraicGeometry.LinearDirectLimitCocone

/-!
概要：代数的順極限と圏論的余極限の比較が、有向系の射に自然であることを示す。
方針：有限段からの標準写像との合成で照合する。
規約：線形写像の可換四角形を、そのまま関手の自然変換にする。
使われ方：閉厚化への実際の制限を F6 の二つの余極限表示で同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u v
variable {R : Type v} [CommRing R] {M N : ℕ → Type u}
variable [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
variable [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]
variable (f : ∀ i j, i ≤ j → M i →ₗ[R] M j)
variable (g : ∀ i j, i ≤ j → N i →ₗ[R] N j)
variable [DirectedSystem M (f · · ·)] [DirectedSystem N (g · · ·)]

/-- 順極限の比較同型は各有限段からの標準写像を保つ。 -/
theorem linearDirectLimitColimitIso_ι (n : ℕ) :
    ModuleCat.ofHom (DirectLimit.Module.of R ℕ M f n) ≫
        (linearDirectLimitColimitIso f).hom =
      colimit.ι (linearDirectSystemFunctor f) n :=
  (linearDirectSystemIsColimit f).comp_coconePointUniqueUpToIso_hom
    (colimit.isColimit (linearDirectSystemFunctor f)) n

variable (a : ∀ n, M n →ₗ[R] N n)
variable (ha : ∀ i j h x, a j (f i j h x) = g i j h (a i x))

/-- 有向系の段ごとの可換写像を関手間の自然変換として読む。 -/
def linearDirectSystemNatTrans : linearDirectSystemFunctor f ⟶ linearDirectSystemFunctor g where
  app n := ModuleCat.ofHom (a n)
  naturality {i j} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact ha i j (leOfHom h) x

/-- 代数的順極限と圏論的余極限の同型は、有向系の射に自然。 -/
theorem linearDirectLimitColimitIso_naturality :
    ModuleCat.ofHom (linearDirectLimitComparison f g a ha) ≫
        (linearDirectLimitColimitIso g).hom =
      (linearDirectLimitColimitIso f).hom ≫
        colim.map (linearDirectSystemNatTrans f g a ha) := by
  apply (linearDirectSystemIsColimit f).hom_ext
  intro n
  change ModuleCat.ofHom (DirectLimit.Module.of R ℕ M f n) ≫ _ = _
  rw [← Category.assoc, show
    ModuleCat.ofHom (DirectLimit.Module.of R ℕ M f n) ≫
        ModuleCat.ofHom (linearDirectLimitComparison f g a ha) =
      ModuleCat.ofHom (a n) ≫ ModuleCat.ofHom (DirectLimit.Module.of R ℕ N g n) from rfl]
  rw [Category.assoc, linearDirectLimitColimitIso_ι]
  change ModuleCat.ofHom (a n) ≫ colimit.ι (linearDirectSystemFunctor g) n =
    ModuleCat.ofHom (DirectLimit.Module.of R ℕ M f n) ≫
      (linearDirectLimitColimitIso f).hom ≫
        colim.map (linearDirectSystemNatTrans f g a ha)
  rw [← Category.assoc, linearDirectLimitColimitIso_ι, colimit.ι_map]
  rfl

end SerrePositivity.AlgebraicGeometry
