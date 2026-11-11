module

public import SerrePositivity.KST.Spectra.RelStructHomotopy
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
概要：境界定数単体の相対ホモトピーと球面の点つき射の基点固定ホモトピーの比較。
方針：境界を潰す pushout を区間との積で移し、相対条件からホモトピーを降ろす。
規約：Kan 性はこの幾何的な構成に不要。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。球面の写像空間の連結成分。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.SphereSimplex

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：球面の基礎単体集合を与える実際の pushout。
方針：cofiber の定義の pushout を使う。
規約：元の境界を単位へ潰す。
使われ方：Goerss–Jardine I §7。基点付き球面の相対ホモトピーの降下。 -/
theorem quotient_isPushout (n : ℕ) : IsPushout (boundary.{u} n).ι
    (toUnit (boundary.{u} n : SSet.{u})) (PointedObject.cofiberQuotient (boundary.{u} n).ι)
      (PointedSimplicialSet.sphere.{u} n).hom :=
  IsPushout.of_hasPushout _ _

/-- 概要：球面の pushout は任意のパラメータとの積で保たれる。
方針：閉対称モノイダル構造の左随伴による pushout 保存を使う。
規約：パラメータ P に有限性や Kan 性を要求しない。
使われ方：Goerss–Jardine I §7。区間族を球面へ降ろす。 -/
theorem quotient_product_isPushout (n : ℕ) (P : SSet.{u}) :
    IsPushout ((boundary.{u} n).ι ▷ P) (toUnit (boundary.{u} n : SSet.{u}) ▷ P)
      (PointedObject.cofiberQuotient (boundary.{u} n).ι ▷ P)
        ((PointedSimplicialSet.sphere.{u} n).hom ▷ P) :=
  (quotient_isPushout n).map (tensorRight P)

/-- 概要：境界固定の単体のホモトピーを球面上の区間族へ降ろす。
方針：区間との積で移した pushout に二つの射を貼る。
規約：基点側では区間全体で同じ基点へ写す。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。球面上の実際のホモトピー。 -/
def descendHomotopy (X : PointedSimplicialSet.{u}) (n : ℕ)
    {s t : X.right.PtSimplex n X.basepoint} (H : s.Homotopy t) :
    (PointedSimplicialSet.sphere.{u} n).right ⊗ (Δ[1] : SSet.{u}) ⟶ X.right := by
  refine (quotient_product_isPushout n (Δ[1] : SSet.{u})).desc H.h
    (toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ X.hom) ?_
  simp only [H.rel, Subcomplex.ofSimplex_ι, SSet.comp_const, comp_toUnit_assoc]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const X _).symm

/-- 概要：降ろしたホモトピーを標準単体へ戻すと元の区間族。
方針：pushout の降下の第一成分の計算を使う。
規約：区間との積の商射を前合成する。
使われ方：Goerss–Jardine I §7。ホモトピーの端点の計算。 -/
@[reassoc]
theorem quotient_descendHomotopy (X : PointedSimplicialSet.{u}) (n : ℕ)
    {s t : X.right.PtSimplex n X.basepoint} (H : s.Homotopy t) :
    PointedObject.cofiberQuotient (boundary.{u} n).ι ▷ (Δ[1] : SSet.{u}) ≫
      descendHomotopy X n H = H.h :=
  (quotient_product_isPushout n (Δ[1] : SSet.{u})).inl_desc _ _ _

/-- 概要：降ろしたホモトピーは全区間で球面の基点を固定する。
方針：pushout の降下の第二成分の計算を使う。
規約：基点側の区間は標的の基点への定数族。
使われ方：Kerodon §3.2.2（Tag 00VJ）。点つきホモトピーとしての相対条件。 -/
@[reassoc]
theorem base_descendHomotopy (X : PointedSimplicialSet.{u}) (n : ℕ)
    {s t : X.right.PtSimplex n X.basepoint} (H : s.Homotopy t) :
    (PointedSimplicialSet.sphere.{u} n).hom ▷ (Δ[1] : SSet.{u}) ≫ descendHomotopy X n H =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ X.hom :=
  (quotient_product_isPushout n (Δ[1] : SSet.{u})).inr_desc _ _ _

/-- 概要：相対単体ホモトピーは球面の点つき射間の実際の区間ホモトピーを与える。
方針：降ろした区間族の両端点を元の pushout の二成分で検査する。
規約：基点固定条件は base_descendHomotopy に保持する。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。相対な代表の等式を写像空間へ移す。 -/
def homotopy (X : PointedSimplicialSet.{u}) (n : ℕ)
    {s t : X.right.PtSimplex n X.basepoint} (H : s.Homotopy t) :
    SSet.Homotopy (toMap X n s).right (toMap X n t).right where
  h := descendHomotopy X n H
  h₀ := by
    apply (quotient_isPushout n).hom_ext
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, quotient_descendHomotopy, H.h₀]
      exact (PointedObject.cofiberQuotient_desc (boundary.{u} n).ι X _ _).symm
    · rw [← Category.assoc, ← SSet.ι₀_comp, Category.assoc, base_descendHomotopy]
      change SSet.ι₀ ≫ (toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ X.hom) =
        (PointedSimplicialSet.sphere.{u} n).hom ≫ (toMap X n s).right
      rw [Under.w (toMap X n s)]
      rfl
  h₁ := by
    apply (quotient_isPushout n).hom_ext
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, quotient_descendHomotopy, H.h₁]
      exact (PointedObject.cofiberQuotient_desc (boundary.{u} n).ι X _ _).symm
    · rw [← Category.assoc, ← SSet.ι₁_comp, Category.assoc, base_descendHomotopy]
      change SSet.ι₁ ≫ (toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ X.hom) =
        (PointedSimplicialSet.sphere.{u} n).hom ≫ (toMap X n t).right
      rw [Under.w (toMap X n t)]
      rfl
  rel := by ext m ⟨⟨z, hz⟩, v⟩; exact hz.elim

/-- 概要：球面の基点固定ホモトピーを、境界定数単体の相対ホモトピーへ引き戻す。
方針：標準単体から商への射を区間全体で前合成し、商の境界の基点条件を使う。
規約：球面の次元は任意。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。写像空間の類から元のホモトピー群へ戻す。 -/
def pullHomotopy (X : PointedSimplicialSet.{u}) (n : ℕ)
    (f g : PointedSimplicialSet.sphere.{u} n ⟶ X) (H : SSet.Homotopy f.right g.right)
    (hH : (PointedSimplicialSet.sphere.{u} n).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ X.hom) :
    (equiv X n f).Homotopy (equiv X n g) where
  h := PointedObject.cofiberQuotient (boundary.{u} n).ι ▷ (Δ[1] : SSet.{u}) ≫ H.h
  h₀ := by
    rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, H.h₀]
    rfl
  h₁ := by
    rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁]
    rfl
  rel := by
    have hH' : (PointedObject.cofiber (boundary.{u} n).ι).hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ X.hom := hH
    rw [← comp_whiskerRight_assoc, PointedObject.cofiberQuotient_condition,
      comp_whiskerRight_assoc, hH']
    simp only [comp_toUnit_assoc, Subcomplex.ofSimplex_ι, SSet.comp_const]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedConstant_eq_const X _

end

end SerrePositivity.KST.Spectra.SphereSimplex
