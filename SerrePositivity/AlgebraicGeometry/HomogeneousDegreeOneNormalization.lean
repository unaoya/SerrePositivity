module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

/-!
概要：次数一の元による斉次局所化への脱斉次化写像。
方針：各次数の x を x/f^n に送り、内部直和の環の普遍性を使う。
規約：非零な分母・平坦性・次数一生成を仮定しない。
使われ方：Segre 標準開の座標比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [GradedRing G] {f : A} (hf : f ∈ G 1)

/-- 次数 n の元を x/f^n に送る加法写像。 -/
def homogeneousDegreeOneNormalizePiece (n : ℕ) :
    G n →+ HomogeneousLocalization.Away G f where
  toFun x := HomogeneousLocalization.Away.mk G hf n x (by simpa using x.property)
  map_zero' := by
    apply HomogeneousLocalization.val_injective (Submonoid.powers f)
    simp [HomogeneousLocalization.val_zero, HomogeneousLocalization.Away.val_mk, Localization.mk_zero]
  map_add' x y := by
    apply HomogeneousLocalization.val_injective (Submonoid.powers f)
    simp only [HomogeneousLocalization.val_add, HomogeneousLocalization.Away.val_mk,
      Submodule.coe_add]
    exact (Localization.add_mk_self _ _ _).symm

/-- 各次数の脱斉次化を実際の環の写像に束ねる。 -/
def homogeneousDegreeOneNormalize : A →+* HomogeneousLocalization.Away G f :=
  (DirectSum.toSemiring (homogeneousDegreeOneNormalizePiece G hf)
    (by
      apply HomogeneousLocalization.val_injective (Submonoid.powers f)
      simp [homogeneousDegreeOneNormalizePiece, HomogeneousLocalization.val_one,
        HomogeneousLocalization.Away.val_mk])
    (by
      intro i j x y
      apply HomogeneousLocalization.val_injective (Submonoid.powers f)
      simp only [homogeneousDegreeOneNormalizePiece, AddMonoidHom.coe_mk,
        HomogeneousLocalization.val_mul, HomogeneousLocalization.Away.val_mk]
      simp [Localization.mk_mul, pow_add])).comp (DirectSum.decomposeRingEquiv G).toRingHom

/-- 斉次元における脱斉次化の式。 -/
theorem homogeneousDegreeOneNormalize_of_mem {n : ℕ} (x : A) (hx : x ∈ G n) :
    homogeneousDegreeOneNormalize G hf x =
      HomogeneousLocalization.Away.mk G hf n x (by simpa using hx) := by
  dsimp only [homogeneousDegreeOneNormalize, RingHom.comp_apply]
  rw [show (DirectSum.decomposeRingEquiv G).toRingHom x = DirectSum.decompose G x from rfl,
    DirectSum.decompose_of_mem G hx, DirectSum.toSemiring_of]
  rfl

/-- 次数一の分母自身は 1 に移る。 -/
theorem homogeneousDegreeOneNormalize_self : homogeneousDegreeOneNormalize G hf f = 1 := by
  rw [homogeneousDegreeOneNormalize_of_mem G hf f hf]
  apply HomogeneousLocalization.val_injective (Submonoid.powers f)
  simp [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one]

end SerrePositivity.AlgebraicGeometry
