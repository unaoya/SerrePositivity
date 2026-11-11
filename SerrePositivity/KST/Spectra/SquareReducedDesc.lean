module

public import SerrePositivity.KST.Spectra.SphereProductDesc
public import SerrePositivity.Spectra.Pointed.ReducedPair

/-!
概要：正方形の四辺で定数な写像を二つの円の smash 積へ降ろす。
方針：二つの境界の商を順に取り、二変数の reduced map を構成する。
規約：座標の順序は最初の区間を第一の円とする。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.3（Tag 00W3）。二つの相対三角形の貼り合わせ。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SphereSimplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (Y : PointedSimplicialSet.{u})
  (f : (Δ[1] : SSet.{u}) ⊗ (Δ[1] : SSet.{u}) ⟶ Y.right)
  (hl : (boundary.{u} 1).ι ▷ (Δ[1] : SSet.{u}) ≫ f =
    toUnit ((boundary.{u} 1 : SSet.{u}) ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom)
  (hr : (Δ[1] : SSet.{u}) ◁ (boundary.{u} 1).ι ≫ f =
    toUnit ((Δ[1] : SSet.{u}) ⊗ (boundary.{u} 1 : SSet.{u})) ≫ Y.hom)

include hr

/-- 概要：一方の境界を潰した族のもう一方の境界も定数である。
方針：パラメータの指定部分での定数性の保存を用いる。
規約：第一の区間だけを円へ降ろした段階。
使われ方：Goerss–Jardine I §7。二つ目の境界の商の存在条件。 -/
theorem firstDesc_boundary :
    (PointedSimplicialSet.circle.{u}).right ◁ (boundary.{u} 1).ι ≫
      productDesc 1 (Δ[1] : SSet.{u}) Y f hl =
        toUnit ((PointedSimplicialSet.circle.{u}).right ⊗
          (boundary.{u} 1 : SSet.{u})) ≫ Y.hom :=
  productDesc_parameter_constant 1 _ _ Y f hl _ hr

/-- 概要：座標を交換した第一の降下は、残る単体方向の境界で定数。
方針：対称性の自然性で境界の射を交換する。
規約：第二の降下の入力では円をパラメータとする。
使われ方：Kerodon §3.2.3（Tag 00W3）。正方形の境界を二方向へ潰す。 -/
theorem firstDesc_swap_boundary :
    (boundary.{u} 1).ι ▷ (PointedSimplicialSet.circle.{u}).right ≫
      (β_ (Δ[1] : SSet.{u}) (PointedSimplicialSet.circle.{u}).right).hom ≫
        productDesc 1 (Δ[1] : SSet.{u}) Y f hl =
      toUnit ((boundary.{u} 1 : SSet.{u}) ⊗
        (PointedSimplicialSet.circle.{u}).right) ≫ Y.hom := by
  rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc,
    firstDesc_boundary Y f hl hr, comp_toUnit_assoc]

/-- 概要：四辺で定数な正方形の写像を二つの円の積へ降ろす。
方針：第一の降下の座標を交換して第二の降下を行い、最後に座標を戻す。
規約：商を取る順序による座標の交換は明示する。
使われ方：Goerss–Jardine I §7。smash 積の普遍性へ渡す二変数の族。 -/
def squareDesc : (PointedSimplicialSet.circle.{u}).right ⊗
    (PointedSimplicialSet.circle.{u}).right ⟶ Y.right :=
  (β_ (PointedSimplicialSet.circle.{u}).right
    (PointedSimplicialSet.circle.{u}).right).hom ≫
      productDesc 1 (PointedSimplicialSet.circle.{u}).right Y
        ((β_ (Δ[1] : SSet.{u}) (PointedSimplicialSet.circle.{u}).right).hom ≫
          productDesc 1 (Δ[1] : SSet.{u}) Y f hl)
        (firstDesc_swap_boundary Y f hl hr)

omit hr in
/-- 概要：座標を交換した第一の降下は、円の基点で定数。
方針：対称性の自然性で基点の射を移し、第一の降下の基点条件を使う。
規約：この段階では残る区間全体で定数となる。
使われ方：Goerss–Jardine I §7。第二の降下の reduced 条件。 -/
theorem firstDesc_swap_base :
    (Δ[1] : SSet.{u}) ◁ PointedSimplicialSet.circle.{u}.hom ≫
      (β_ (Δ[1] : SSet.{u}) (PointedSimplicialSet.circle.{u}).right).hom ≫
        productDesc 1 (Δ[1] : SSet.{u}) Y f hl =
      toUnit ((Δ[1] : SSet.{u}) ⊗ 𝟙_ SSet.{u}) ≫ Y.hom := by
  rw [← Category.assoc, BraidedCategory.braiding_naturality_right, Category.assoc]
  erw [base_productDesc, comp_toUnit_assoc]

/-- 概要：二重の降下は第一の円の基点上で定数。
方針：第二の降下のパラメータ定数性を使う。
規約：第一の変数を基点に制限する。
使われ方：Kerodon §3.2.3（Tag 00W3）。smash への降下の第一条件。 -/
theorem squareDesc_base_left :
    PointedSimplicialSet.circle.{u}.hom ▷ PointedSimplicialSet.circle.{u}.right ≫
      squareDesc Y f hl hr =
        toUnit (𝟙_ SSet.{u} ⊗ PointedSimplicialSet.circle.{u}.right) ≫ Y.hom := by
  dsimp only [squareDesc]
  rw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc]
  erw [productDesc_parameter_constant 1 _ _ Y _ _ _ (firstDesc_swap_base Y f hl),
    comp_toUnit_assoc]

/-- 概要：二重の降下は第二の円の基点上で定数。
方針：第二の降下の球面の基点条件を使う。
規約：第二の変数を基点に制限する。
使われ方：Kerodon §3.2.3（Tag 00W3）。smash への降下の第二条件。 -/
theorem squareDesc_base_right :
    PointedSimplicialSet.circle.{u}.right ◁ PointedSimplicialSet.circle.{u}.hom ≫
      squareDesc Y f hl hr =
        toUnit (PointedSimplicialSet.circle.{u}.right ⊗ 𝟙_ SSet.{u}) ≫ Y.hom := by
  dsimp only [squareDesc]
  rw [← Category.assoc, BraidedCategory.braiding_naturality_right, Category.assoc]
  erw [base_productDesc, comp_toUnit_assoc]

/-- 概要：四辺で定数な正方形の写像は二つの円の smash 積からの射となる。
方針：二重の降下の両軸の定数性を reduced map としてまとめる。
規約：標的の Kan 性は不要。
使われ方：Goerss–Jardine I §7、BF 1978 §2。相対三角形の貼り合わせからの射。 -/
def squareSmashDesc : PointedObject.smash PointedSimplicialSet.circle.{u}
    PointedSimplicialSet.circle.{u} ⟶ Y :=
  PointedObject.reducedToSmash ⟨squareDesc Y f hl hr,
    squareDesc_base_left Y f hl hr, squareDesc_base_right Y f hl hr⟩

/-- 概要：二つの円の積へ降ろした写像は正方形上で元の写像に一致する。
方針：対称性の自然性で二つの商射を移し、降下の標準射の式を二度使う。
規約：二つの区間の座標の順序を保つ。
使われ方：Goerss–Jardine I §7。境界を潰した正方形の普遍性の計算。 -/
@[reassoc]
theorem squareDesc_quotient :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
      PointedObject.cofiberQuotient (boundary.{u} 1).ι) ≫ squareDesc Y f hl hr = f := by
  dsimp only [squareDesc]
  erw [tensorHom_def, Category.assoc, BraidedCategory.braiding_naturality_right_assoc]
  erw [← Category.assoc, BraidedCategory.braiding_naturality_left, Category.assoc,
    quotient_productDesc, BraidedCategory.braiding_naturality_right_assoc]
  simp only [← Category.assoc, SymmetricCategory.symmetry, Category.id_comp]
  exact quotient_productDesc 1 _ Y f hl

/-- 概要：smash 積への降下を正方形へ戻すと元の写像となる。
方針：smash の商での計算と二重の球面の商での計算を合わせる。
規約：等式は基礎単体集合の実際の射の等式。
使われ方：Goerss–Jardine I §7。正方形の境界の商の標準射の計算。 -/
@[reassoc]
theorem squareSmashDesc_quotient :
    (PointedObject.cofiberQuotient (boundary.{u} 1).ι ⊗ₘ
      PointedObject.cofiberQuotient (boundary.{u} 1).ι) ≫
        (PointedObject.smashQuotient PointedSimplicialSet.circle.{u}
          PointedSimplicialSet.circle.{u}).right ≫ (squareSmashDesc Y f hl hr).right = f := by
  have h : (PointedObject.smashQuotient PointedSimplicialSet.circle.{u}
      PointedSimplicialSet.circle.{u}).right ≫ (squareSmashDesc Y f hl hr).right =
        squareDesc Y f hl hr :=
    congrArg Subtype.val
      ((PointedObject.smashReducedHomEquiv PointedSimplicialSet.circle.{u}
        PointedSimplicialSet.circle.{u} Y).apply_symm_apply
          ⟨squareDesc Y f hl hr, squareDesc_base_left Y f hl hr,
            squareDesc_base_right Y f hl hr⟩)
  rw [h]
  exact squareDesc_quotient Y f hl hr

end

end SerrePositivity.KST.Spectra.SphereSimplex
