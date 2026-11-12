module

public import SerrePositivity.KST.Spectra.SphereHomotopy

/-!
概要：境界で定数なパラメータ族を球面との積へ降ろす。
方針：積で保存した商の pushout の普遍性を用いる。
規約：パラメータにも標的にも Kan 性を要求しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。正方形の境界を順に潰す構成。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SphereSimplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：単体方向の境界が定数な族を球面へ降ろす。
方針：商の pushout に元の族と基点の定数族を貼る。
規約：任意の単体次数と任意のパラメータを許す。
使われ方：Goerss–Jardine I §7。二変数の境界の逐次的な商。 -/
def productDesc (n : ℕ) (P : SSet.{u}) (Y : PointedSimplicialSet.{u})
    (f : (Δ[n] : SSet.{u}) ⊗ P ⟶ Y.right)
    (hf : (boundary.{u} n).ι ▷ P ≫ f =
      toUnit ((boundary.{u} n : SSet.{u}) ⊗ P) ≫ Y.hom) :
    (PointedSimplicialSet.sphere.{u} n).right ⊗ P ⟶ Y.right :=
  (quotient_product_isPushout n P).desc f
    (toUnit (𝟙_ SSet.{u} ⊗ P) ≫ Y.hom) (by simpa using hf)

/-- 概要：商へ降ろした族を単体へ戻すと元の族となる。
方針：pushout の第一の脚で計算する。
規約：商射を単体方向へ前合成する。
使われ方：Kerodon §3.2.3（Tag 00W3）。商の上の等式の確認。 -/
@[reassoc (attr := simp)]
theorem quotient_productDesc (n : ℕ) (P : SSet.{u}) (Y : PointedSimplicialSet.{u})
    (f : (Δ[n] : SSet.{u}) ⊗ P ⟶ Y.right) (hf) :
    PointedObject.cofiberQuotient (boundary.{u} n).ι ▷ P ≫ productDesc n P Y f hf = f :=
  (quotient_product_isPushout n P).inl_desc _ _ _

/-- 概要：球面の基点ではパラメータ全体で定数となる。
方針：pushout の第二の脚で計算する。
規約：定数の値は標的の指定基点。
使われ方：Goerss–Jardine I §7。点つきの降下の基点条件。 -/
@[reassoc (attr := simp)]
theorem base_productDesc (n : ℕ) (P : SSet.{u}) (Y : PointedSimplicialSet.{u})
    (f : (Δ[n] : SSet.{u}) ⊗ P ⟶ Y.right) (hf) :
    (PointedSimplicialSet.sphere.{u} n).hom ▷ P ≫ productDesc n P Y f hf =
      toUnit (𝟙_ SSet.{u} ⊗ P) ≫ Y.hom :=
  (quotient_product_isPushout n P).inr_desc _ _ _

/-- 概要：パラメータの指定部分での定数性は球面への降下で保たれる。
方針：指定部分との積の pushout の両脚で等式を検査する。
規約：指定部分の射に単射性を要求しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。二つ目の境界を潰す条件。 -/
theorem productDesc_parameter_constant (n : ℕ) (P Q : SSet.{u})
    (Y : PointedSimplicialSet.{u}) (f : (Δ[n] : SSet.{u}) ⊗ P ⟶ Y.right) (hf)
    (i : Q ⟶ P)
    (hi : (Δ[n] : SSet.{u}) ◁ i ≫ f = toUnit ((Δ[n] : SSet.{u}) ⊗ Q) ≫ Y.hom) :
    (PointedSimplicialSet.sphere.{u} n).right ◁ i ≫ productDesc n P Y f hf =
      toUnit ((PointedSimplicialSet.sphere.{u} n).right ⊗ Q) ≫ Y.hom := by
  apply (quotient_product_isPushout n Q).hom_ext
  · erw [← Category.assoc, ← whisker_exchange, Category.assoc, quotient_productDesc]
    erw [comp_toUnit_assoc]
    exact hi
  · erw [← Category.assoc, ← whisker_exchange, Category.assoc, base_productDesc]
    erw [comp_toUnit_assoc, comp_toUnit_assoc]

end

end SerrePositivity.KST.Spectra.SphereSimplex
