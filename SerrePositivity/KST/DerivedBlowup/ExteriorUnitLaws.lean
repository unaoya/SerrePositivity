module

public import SerrePositivity.KST.DerivedBlowup.ExteriorUnit
public import SerrePositivity.DifferentialGraded.Complexes.Braiding

/-!
概要：KST Def3.1 の Koszul 外積複体の左右単位則。
方針：単位制約の逆を純粋 tensor で計算し、総外積への単射で比較する。
規約：既存 Ch(R) のモノイダル制約を使う。
使われ方：Koszul チャートの一対象 dg 圏の圏法則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory MonoidalCategory HomologicalComplex

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：乗法の純粋同次 tensor の値は同次外積。
方針：tensorLift の成分公式を評価する。
規約：KST Def3.1。使われ方：単位則と結合則。 -/
theorem exteriorKoszulMultiplication_apply (d : M →ₗ[R] R)
    (p q n : ℤ) (h : p + q = n)
    (x : (exteriorKoszulCochain d).X p) (y : (exteriorKoszulCochain d).X q) :
    (exteriorKoszulMultiplication d).f n
        (ιTensorObj (exteriorKoszulCochain d) (exteriorKoszulCochain d)
          p q n h (x ⊗ₜ[R] y)) =
      exteriorCochainBilinear d p q n h x y :=
  congr($(exteriorKoszulMultiplication_component d p q n h).hom (x ⊗ₜ[R] y))

/-- 概要：Koszul 外積複体の左単位則。
方針：左単位制約と乗法を評価し、総外積で 1x=x を使う。
規約：KST Def3.1。使われ方：dg 圏の id_comp。 -/
theorem exteriorKoszul_left_unit (d : M →ₗ[R] R) :
    (λ_ (exteriorKoszulCochain d)).inv ≫ exteriorKoszulUnit d ▷ _ ≫
      exteriorKoszulMultiplication d = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hv := congr($(leftUnitor'_inv (exteriorKoszulCochain d) n).hom x)
  change (λ_ (exteriorKoszulCochain d)).inv.f n x =
    ιTensorObj (𝟙_ (DifferentialGraded.Complex R)) (exteriorKoszulCochain d)
      0 n n (zero_add n) ((1 : R) ⊗ₜ[R] x) at hv
  change (exteriorKoszulMultiplication d).f n
    ((exteriorKoszulUnit d ▷ _).f n
      ((λ_ (exteriorKoszulCochain d)).inv.f n x)) = x
  rw [hv, DifferentialGraded.whiskerRight_apply, exteriorKoszulMultiplication_apply]
  apply exteriorCochainInclusion_injective d n
  rw [exteriorCochainInclusion_product, exteriorKoszulUnit_inclusion, map_one, one_mul]

/-- 概要：Koszul 外積複体の右単位則。
方針：右単位制約と乗法を評価し、総外積で x1=x を使う。
規約：KST Def3.1。使われ方：dg 圏の comp_id。 -/
theorem exteriorKoszul_right_unit (d : M →ₗ[R] R) :
    (ρ_ (exteriorKoszulCochain d)).inv ≫ _ ◁ exteriorKoszulUnit d ≫
      exteriorKoszulMultiplication d = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hv := congr($(rightUnitor'_inv (exteriorKoszulCochain d) n).hom x)
  change (ρ_ (exteriorKoszulCochain d)).inv.f n x =
    ιTensorObj (exteriorKoszulCochain d) (𝟙_ (DifferentialGraded.Complex R))
      n 0 n (add_zero n) (x ⊗ₜ[R] (1 : R)) at hv
  change (exteriorKoszulMultiplication d).f n
    ((_ ◁ exteriorKoszulUnit d).f n
      ((ρ_ (exteriorKoszulCochain d)).inv.f n x)) = x
  rw [hv, DifferentialGraded.whiskerLeft_apply, exteriorKoszulMultiplication_apply]
  apply exteriorCochainInclusion_injective d n
  rw [exteriorCochainInclusion_product, exteriorKoszulUnit_inclusion, map_one, mul_one]

end SerrePositivity.KST.DerivedBlowup
