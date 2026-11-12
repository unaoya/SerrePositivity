module
public import SerrePositivity.KST.SConstruction.DGFunctorNativeSimplexCoherence

/-! # native Kan 写像空間の実横合成の結合・単位
概要：元の全高次関手族の横合成と恒等頂点を、Kan 写像空間の厳密な法則に束ねる。
方針：部分型の値で全単体の元の結合・単位を使い、単位射は元の恒等頂点から作る。
規約：単位は元の閉単位と増大を回収。使われ方：厳密 dg 入力の単体的豊穣圏。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Opposite Simplicial SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A] (D E B T : Type v)
  [DGCategory A D] [DGCategory A E] [DGCategory A B] [DGCategory A T]
  [Small.{u} D] [Small.{u} E] [Small.{u} B]

/-- native Kan 写像空間の実横合成は、元の直積の結合同型を介して厳密に結合的。 -/
lemma dgFunctorNativeComposition_associativity :
    (dgFunctorNativeComposition A D E B ⊗ₘ 𝟙 (dgFunctorNativeMappingSpace A B T)) ≫
        dgFunctorNativeComposition A D B T =
      (α_ (dgFunctorNativeMappingSpace A D E) (dgFunctorNativeMappingSpace A E B)
        (dgFunctorNativeMappingSpace A B T)).hom ≫
        (𝟙 (dgFunctorNativeMappingSpace A D E) ⊗ₘ dgFunctorNativeComposition A E B T) ≫
        dgFunctorNativeComposition A D E T := by
  ext n p
  rcases p with ⟨⟨s, t⟩, r⟩
  apply Subtype.ext
  exact dgFunctorNativeComposeSimplex_associativity A D E B T s.val t.val r.val

omit [DGCategory A E] [DGCategory A B] [DGCategory A T] [Small.{u} E] [Small.{u} B] in
/-- 元の恒等 dg 関手の頂点から作る、native Kan 写像空間の実単位射。 -/
def dgFunctorNativeIdentity : 𝟙_ SSet.{max u v} ⟶ dgFunctorNativeMappingSpace A D D :=
  (SSet.unitHomEquiv (dgFunctorNativeMappingSpace A D D)).symm
    (dgFunctorNativeMappingVertex A D D (DGFunctor.id D))

omit [DGCategory A E] [DGCategory A B] [DGCategory A T] [Small.{u} E] [Small.{u} B] in
/-- 実単位射の各単体は、元の増大・閉単位による native 単位単体を回収する。 -/
lemma dgFunctorNativeIdentity_app (n : SimplexCategoryᵒᵖ) (x : (𝟙_ SSet.{max u v}).obj n) :
    ((dgFunctorNativeIdentity A D).app n x).val =
      dgFunctorNativeIdentitySimplex A D n.unop.len := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (DGFunctor.id D)).pullback
    (SimplexCategory.const n.unop ⦋0⦌ 0).toOrderHom = _
  rw [← dgFunctorNativeIdentitySimplex_zero]
  exact dgFunctorNativeIdentitySimplex_pullback A D _

omit [DGCategory A B] [DGCategory A T] [Small.{u} B] [Small.{u} E] in
/-- native Kan 写像空間の元の実単位射は、左横合成で元の単体的左単位を回収する。 -/
lemma dgFunctorNativeComposition_left_unit :
    (dgFunctorNativeIdentity A D ⊗ₘ 𝟙 (dgFunctorNativeMappingSpace A D E)) ≫
        dgFunctorNativeComposition A D D E = (λ_ (dgFunctorNativeMappingSpace A D E)).hom := by
  ext n p
  rcases p with ⟨a, s⟩
  apply Subtype.ext
  change dgFunctorNativeComposeSimplex A D D E
    (((dgFunctorNativeIdentity A D).app n a).val) s.val = s.val
  rw [dgFunctorNativeIdentity_app]
  exact dgFunctorNativeComposeSimplex_left_unit A D E s.val

omit [DGCategory A B] [DGCategory A T] [Small.{u} B] in
/-- native Kan 写像空間の元の実単位射は、右横合成で元の単体的右単位を回収する。 -/
lemma dgFunctorNativeComposition_right_unit :
    (𝟙 (dgFunctorNativeMappingSpace A D E) ⊗ₘ dgFunctorNativeIdentity A E) ≫
        dgFunctorNativeComposition A D E E = (ρ_ (dgFunctorNativeMappingSpace A D E)).hom := by
  ext n p
  rcases p with ⟨s, a⟩
  apply Subtype.ext
  change dgFunctorNativeComposeSimplex A D E E s.val
    (((dgFunctorNativeIdentity A E).app n a).val) = s.val
  rw [dgFunctorNativeIdentity_app]
  exact dgFunctorNativeComposeSimplex_right_unit A D E s.val

end SerrePositivity.KST.SConstruction
