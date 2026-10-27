module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.QuotientEpsilonHorizontal

/-!
概要：固定 ε 整合関手の横合成を dg 関手へ束ね、正本商作用との厳密交換を示す。
方針：同じ成分の着地 API を適用し、商側の等号移送を相殺する。
規約：Hom 複体全体の等号を保持する。
使われ方：native core 上の全単体の横合成保存。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory DifferentialGraded KST.SConstruction
private lemma transportPairCancel (R : Type u) [CommRing R]
    (X : Type v) [DGCategory R X] [Small.{u} X] (Y : Type w) [DGCategory R Y]
    {F G F' G' : DGFunctor R X Y} (hF : F = F') (hG : G = G') :
    dgFunctorHomTransport R X Y hF.symm hG.symm ≫
      dgFunctorHomTransport R X Y hF hG = 𝟙 _ := by
  cases hF
  cases hG
  simp only [dgFunctorHomTransport, eqToHom_refl, Category.id_comp]

variable (R : Type u) [CommRing R]
  (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D]
  (E : Type t) [DGCategory R E] [Small.{u} E]
  (S : Set C) (T : Set D) (U : Set E)

/-- 固定 ε 整合の全 Hom を持つ関手の厳密な横合成。 -/
def quotientEpsilonHorizontalFunctor :
    DGFunctor R (DGTensorCategory R (NullPreservingFunctorsε R C D S T)
      (NullPreservingFunctorsε R D E T U)) (NullPreservingFunctorsε R C E S U) :=
  nullPreservingFunctorsεLiftOfComponents R C E S U _
    (quotientEpsilonHorizontalUnderlying R C D E S T U)
    (quotientEpsilonHorizontal_preserves R C D E S T U)
    (quotientEpsilonHorizontalExtension R C D E S T U)
    (quotientEpsilonHorizontal_components R C D E S T U)

/-- 横合成の商上の全 Hom 作用は、同じ対象へ移送した延長である。 -/
lemma quotientEpsilonHorizontalFunctor_map_extension
    (x y : DGTensorCategory R (NullPreservingFunctorsε R C D S T)
      (NullPreservingFunctorsε R D E T U)) :
    (quotientEpsilonHorizontalFunctor R C D E S T U).map x y ≫
      quotientEpsilonHomExtension R C E S U
        (quotientEpsilonHorizontalObject R C D E S T U x)
        (quotientEpsilonHorizontalObject R C D E S T U y) =
      quotientEpsilonHorizontalExtension R C D E S T U x y :=
  nullPreservingFunctorsεLiftOfComponents_map_extension R C E S U _
    (quotientEpsilonHorizontalUnderlying R C D E S T U)
    (quotientEpsilonHorizontal_preserves R C D E S T U)
    (quotientEpsilonHorizontalExtension R C D E S T U)
    (quotientEpsilonHorizontal_components R C D E S T U) x y

/-- 商上の横合成は、元の横合成後の正本商作用と dg 関手全体で厳密一致する。
同じ Hom end の等号移送を互いに相殺する。 -/
lemma quotientEpsilonHorizontalFunctor_quotient :
    (quotientEpsilonHorizontalFunctor R C D E S T U).comp (quotientInputFunctor R C E S U) =
      ((quotientInputFunctor R C D S T).tensor (quotientInputFunctor R D E T U)).comp
        (dgFunctorHorizontalDG R (DGQuotient.QuotientObject C S)
          (DGQuotient.QuotientObject D T) (DGQuotient.QuotientObject E U)) := by
  apply EnrichedFunctor.ext (Complex R)
    (quotientEpsilonHorizontal_object R C D E S T U)
  intro x y
  change ((quotientEpsilonHorizontalFunctor R C D E S T U).map x y ≫
    quotientEpsilonHomExtension R C E S U
      (quotientEpsilonHorizontalObject R C D E S T U x)
      (quotientEpsilonHorizontalObject R C D E S T U y)) ≫
    dgFunctorHomTransport R _ _
      (quotientEpsilonHorizontal_object R C D E S T U x)
      (quotientEpsilonHorizontal_object R C D E S T U y) =
    (quotientEpsilonHomExtension R C D S T x.1 y.1 ⊗ₘ
      quotientEpsilonHomExtension R D E T U x.2 y.2) ≫
      dgFunctorHorizontal R _ _ _
        (quotientEpsilonObject R C D S T x.1) (quotientEpsilonObject R C D S T y.1)
        (quotientEpsilonObject R D E T U x.2) (quotientEpsilonObject R D E T U y.2)
  rw [quotientEpsilonHorizontalFunctor_map_extension R C D E S T U x y]
  unfold quotientEpsilonHorizontalExtension
  simp only [Category.assoc]
  rw [transportPairCancel R _ _
    (quotientEpsilonHorizontal_object R C D E S T U x)
    (quotientEpsilonHorizontal_object R C D E S T U y), Category.comp_id]

end SerrePositivity.InfinityCategories
