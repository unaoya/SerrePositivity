module

public import SerrePositivity.KST.DerivedBlowup.ExteriorCochainLeibniz
public import SerrePositivity.DifferentialGraded.Complexes.Composition

/-!
概要：KST Def3.1 の整数次数 Koszul 外積複体に chain map としての積を装備する。
方針：双次数の外積を tensorLift に渡し、証明済みの cochain Leibniz 則を使う。
規約：既存 DifferentialGraded.Complexes の tensor と整数符号を使う。
使われ方：Koszul チャートを一対象 dg 圏にする際の合成写像。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex

variable {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]

/-- 概要：Koszul 積の双次数 tensor 成分。
方針：双線形な同次積を TensorProduct.lift で線形化する。
規約：KST Def3.1、p+q=n。使われ方：全 tensor からの積の構成。 -/
def exteriorMultiplicationComponent (d : M →ₗ[R] R) (p q n : ℤ) (h : p + q = n) :
    (exteriorKoszulCochain d).X p ⊗ (exteriorKoszulCochain d).X q ⟶
      (exteriorKoszulCochain d).X n :=
  ModuleCat.ofHom (TensorProduct.lift (exteriorCochainBilinear d p q n h))

/-- 概要：Koszul 積の双次数成分は tensor 微分と可換。
方針：純粋 tensor で既存の cochain Leibniz 則へ帰着する。
規約：KST Def3.1、符号は第一因子の次数。使われ方：tensorLift の chain 条件。 -/
theorem exteriorMultiplicationComponent_d (d : M →ₗ[R] R) (p q : ℤ) :
    exteriorMultiplicationComponent d p q (p + q) rfl ≫
        (exteriorKoszulCochain d).d (p + q) (p + q + 1) =
      ((exteriorKoszulCochain d).d p (p + 1) ▷ (exteriorKoszulCochain d).X q) ≫
          exteriorMultiplicationComponent d (p + 1) q (p + q + 1) (by omega) +
        p.negOnePow • (((exteriorKoszulCochain d).X p ◁
            (exteriorKoszulCochain d).d q (q + 1)) ≫
          exteriorMultiplicationComponent d p (q + 1) (p + q + 1) (by omega)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  change ((exteriorKoszulCochain d).d (p + q) (p + q + 1)).hom
      (exteriorCochainBilinear d p q (p + q) rfl x y) =
    exteriorCochainBilinear d (p + 1) q (p + q + 1) (by omega)
        (((exteriorKoszulCochain d).d p (p + 1)).hom x) y +
      p.negOnePow • exteriorCochainBilinear d p (q + 1) (p + q + 1) (by omega)
        x (((exteriorKoszulCochain d).d q (q + 1)).hom y)
  exact exteriorCochainBilinear_d d p q (p + q) rfl x y

/-- 概要：整数次数 Koszul 外積複体の chain map としての乗法。
方針：双次数成分と微分比較を既存 tensorLift へ渡す。
規約：KST Def3.1、有限生成性は不要。使われ方：Koszul dg 代数の合成写像。 -/
def exteriorKoszulMultiplication (d : M →ₗ[R] R) :
    exteriorKoszulCochain d ⊗ exteriorKoszulCochain d ⟶ exteriorKoszulCochain d :=
  DifferentialGraded.tensorLift (exteriorMultiplicationComponent d)
    (exteriorMultiplicationComponent_d d)

/-- 概要：全 tensor 上の乗法の同次成分は指定した外積積。
方針：tensorLift の直和成分の公式を使う。
規約：KST Def3.1。使われ方：dg 代数の単位・結合則と基底変換の乗法保存。 -/
@[reassoc] theorem exteriorKoszulMultiplication_component (d : M →ₗ[R] R)
    (p q n : ℤ) (h : p + q = n) :
    ιTensorObj (exteriorKoszulCochain d) (exteriorKoszulCochain d) p q n h ≫
        (exteriorKoszulMultiplication d).f n = exteriorMultiplicationComponent d p q n h :=
  DifferentialGraded.ι_tensorLift _ _ p q n h

end SerrePositivity.KST.DerivedBlowup
