module

public import SerrePositivity.BhattScholze.PerfectoidizationInterface.LimitData
public import SerrePositivity.InfinityCategories.Core.Pullback
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

/-! # 通常の商図式からの単体的 excision 四角形

概要：元の四辺とその可換性を、二つの二単体として同時に保持する。
方針：通常の nerve の合成二単体を対角で貼り、単体的関手で写す。
規約：右下は通常の商 T/IT。導来テンソル積には置き換えない。
使われ方：E3 界面の excision 欄。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.PerfectoidizationInterface
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
variable (R : Type u) [CommRing R]

/-- 可換性の証明を共有する二つの合成二単体を、正方形へ貼り合わせる。 -/
def ordinarySquare {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d) :
    (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ algebraNerve R :=
  square_isPushout.desc
    (SSet.yonedaEquiv.symm (ComposableArrows.mk₂ b d))
    (SSet.yonedaEquiv.symm (ComposableArrows.mk₂ a c)) (by
      apply SSet.yonedaEquiv.injective
      change (nerve (A_R R)).δ 1 (ComposableArrows.mk₂ b d) =
        (nerve (A_R R)).δ 1 (ComposableArrows.mk₂ a c)
      rw [CategoryTheory.nerve.δ₁_mk₂_eq, CategoryTheory.nerve.δ₁_mk₂_eq, w])

/-- 四角形の上側の三角形は、元の左辺と下辺の合成二単体。 -/
theorem ordinarySquare_triangle_zero {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d) :
    squareTriangle 0 ≫ ordinarySquare R a b c d w =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₂ b d) :=
  square_isPushout.inl_desc _ _ _

/-- 四角形の下側の三角形は、元の上辺と右辺の合成二単体。 -/
theorem ordinarySquare_triangle_one {A B C D : A_R R} (a : A ⟶ B) (b : A ⟶ C)
    (c : B ⟶ D) (d : C ⟶ D) (w : a ≫ c = b ≫ d) :
    squareTriangle 1 ≫ ordinarySquare R a b c d w =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₂ a c) :=
  square_isPushout.inr_desc _ _ _

/-- 通常の商環に、元の構造射を通した R 作用を与える。 -/
def quotientAlgebra (S : A_R R) (I : Ideal S.right) : A_R R :=
  Under.mk (S.hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I))

/-- 元の通常の商環への射。 -/
def quotientProjection (S : A_R R) (I : Ideal S.right) : S ⟶ quotientAlgebra R S I :=
  Under.homMk (CommRingCat.ofHom (Ideal.Quotient.mk I)) rfl

/-- 下辺は、指定した f から誘導される通常の商の射。 -/
def quotientComparison {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    quotientAlgebra R S I ⟶ quotientAlgebra R T (I.map f.right.hom) :=
  Under.homMk (CommRingCat.ofHom (Ideal.quotientMap (I.map f.right.hom)
    f.right.hom Ideal.le_comap_map)) (by
      change (S.hom ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ _ = T.hom ≫ _
      rw [← Under.w f, Category.assoc, Category.assoc]
      congr 1)

/-- 四辺の可換性は、元の商の射と元の f についての等式。 -/
theorem quotientSquare_commutes {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    f ≫ quotientProjection R T (I.map f.right.hom) =
      quotientProjection R S I ≫ quotientComparison R f I := by
  ext1
  ext x
  rfl

/-- 通常の商による四角形を、可換性の二単体込みで P により写す。 -/
def perfdSquare (P : algebraNerve R ⟶ derivedInfinityCategory R)
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ derivedInfinityCategory R :=
  ordinarySquare R f (quotientProjection R S I)
    (quotientProjection R T (I.map f.right.hom)) (quotientComparison R f I)
    (quotientSquare_commutes R f I) ≫ P

/-- perfectoid 化の四角形の一方の二単体は、元の二つの商の射の像。 -/
theorem perfdSquare_triangle_zero (P : algebraNerve R ⟶ derivedInfinityCategory R)
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    squareTriangle 0 ≫ perfdSquare R P f I =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₂
        (quotientProjection R S I) (quotientComparison R f I)) ≫ P := by
  rw [perfdSquare, ← Category.assoc, ordinarySquare_triangle_zero]

/-- もう一方の二単体は、元の f と右側の商射の像。 -/
theorem perfdSquare_triangle_one (P : algebraNerve R ⟶ derivedInfinityCategory R)
    {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) :
    squareTriangle 1 ≫ perfdSquare R P f I =
      SSet.yonedaEquiv.symm (ComposableArrows.mk₂ f
        (quotientProjection R T (I.map f.right.hom))) ≫ P := by
  rw [perfdSquare, ← Category.assoc, ordinarySquare_triangle_one]

/-- 既存 excision 入力と同じ階数1付値環への一意延長条件。 -/
def ArcOutside (p : ℕ) {S T : A_R R} (f : S ⟶ T) (I : Ideal S.right) : Prop :=
  ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V],
    ringKrullDim V = 1 → IsAdicComplete (Ideal.span {(p : V)}) V →
    ∀ k : S.right →+* V, ¬ (I ≤ RingHom.ker k) →
      ∃! l : T.right →+* V, l.comp f.right.hom = k

end SerrePositivity.BhattScholze.PerfectoidizationInterface
