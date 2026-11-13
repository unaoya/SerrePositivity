module

public import SerrePositivity.AlgebraicGeometry.LinearDirectLimitNaturality
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
概要：代数的順極限の全単射判定を、同じ有向系の圏論的余極限の射へ移す。
方針：自然な比較同型による共役として実際の射を書く。
規約：対象の同型だけでなく、指定した段ごとの写像の余極限を扱う。
使われ方：F6 の正次数の判定を filtered 余極限と Čech H の比較へ渡す。
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
variable (a : ∀ n, M n →ₗ[R] N n)
variable (ha : ∀ i j h x, a j (f i j h x) = g i j h (a i x))

/-- 代数的順極限の比較が全単射なら、同じ射の圏論的余極限も全単射。 -/
theorem linearDirectSystemColimitMap_bijective
    (hb : Function.Bijective (linearDirectLimitComparison f g a ha)) :
    Function.Bijective (colim.map (linearDirectSystemNatTrans f g a ha)).hom := by
  let b := ModuleCat.ofHom (linearDirectLimitComparison f g a ha)
  have : IsIso b := (ConcreteCategory.isIso_iff_bijective b).mpr hb
  have he : colim.map (linearDirectSystemNatTrans f g a ha) =
      (linearDirectLimitColimitIso f).inv ≫ b ≫ (linearDirectLimitColimitIso g).hom := by
    rw [show b ≫ (linearDirectLimitColimitIso g).hom =
        (linearDirectLimitColimitIso f).hom ≫
          colim.map (linearDirectSystemNatTrans f g a ha) from
        linearDirectLimitColimitIso_naturality f g a ha]
    simp only [Iso.inv_hom_id_assoc]
  have : IsIso (colim.map (linearDirectSystemNatTrans f g a ha)) := by
    rw [he]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

end SerrePositivity.AlgebraicGeometry
