module
public import SerrePositivity.DifferentialGraded.Morita.Criterion

/-! # Perf Morita逆関手と一般右随伴の比較

## 概要
他担当のPerf同値の逆関手を、主導来圏への包含後に一般右随伴と比較する。

## 方針
Perf同値の作用比較と余単位から順方向の同型を作り、実際の導来随伴で転置する。

## 規約と注意
三条件と両側compact生成を明示する。列そのものの射影性や局所Hom条件は不要。

## 使われ方
U16cのPerf・全導来圏双方の逆関手を同じ右随伴へ統合する。
-/
@[expose] public section
noncomputable section
universe u v w z z'
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A]
  (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (K : Kernel A D E) (hK : CriterionPerfConditions A D E K)
  {I : Type z} [Small.{u} I] (G : I → DerivedModuleCategory A D)
  (hG : CriterionDerivedCompactGeneration A D G)
  {J : Type z'} [Small.{u} J] (H : J → DerivedModuleCategory A E)
  (hH : CriterionDerivedCompactGeneration A E H)

/-- Perf判定の逆関手に実際の主作用を続けると終域Perfの包含になる。 -/
def kernelMoritaPerfInverseActionIso :
    ((criterionPerfEquivalenceOfConditions A D E K hK).equivalence.inverse ⋙
      perfectModuleInclusion A D Set.univ) ⋙ kernelDerivedTensor A D E K ≅
      perfectModuleInclusion A E Set.univ :=
  let W := criterionPerfEquivalenceOfConditions A D E K hK
  associator W.equivalence.inverse (perfectModuleInclusion A D Set.univ)
      (kernelDerivedTensor A D E K) ≪≫
    isoWhiskerLeft W.equivalence.inverse W.comparison ≪≫
    (associator W.equivalence.inverse W.equivalence.functor
      (perfectModuleInclusion A E Set.univ)).symm ≪≫
    isoWhiskerRight W.equivalence.counitIso (perfectModuleInclusion A E Set.univ) ≪≫
    leftUnitor (perfectModuleInclusion A E Set.univ)

/-- Perf判定の逆関手は、包含後に実際の一般右随伴へ自然同型である。 -/
def kernelMoritaPerfInverseIso :
    (criterionPerfEquivalenceOfConditions A D E K hK).equivalence.inverse ⋙
      perfectModuleInclusion A D Set.univ ≅
    perfectModuleInclusion A E Set.univ ⋙ kernelDerivedHom A D E K :=
  let S := (criterionPerfEquivalenceOfConditions A D E K hK).equivalence.inverse ⋙
    perfectModuleInclusion A D Set.univ
  let e := kernelMoritaAdjunctionEquivalence A D E K hK G hG H hH
  (rightUnitor S).symm ≪≫ isoWhiskerLeft S e.unitIso ≪≫
    (associator S (kernelDerivedTensor A D E K) (kernelDerivedHom A D E K)).symm ≪≫
    isoWhiskerRight (kernelMoritaPerfInverseActionIso A D E K hK) (kernelDerivedHom A D E K)

/-- Perf逆関手の比較は、実際の随伴の余単位で元の作用比較を計算する。 -/
lemma kernelMoritaPerfInverseIso_counit (X : PerfectModuleCategory A E) :
    (kernelDerivedTensor A D E K).map
        ((kernelMoritaPerfInverseIso A D E K hK G hG H hH).hom.app X) ≫
      (kernelDerivedCounit A D E K).app ((perfectModuleInclusion A E Set.univ).obj X) =
    (kernelMoritaPerfInverseActionIso A D E K hK).hom.app X := by
  let S := (criterionPerfEquivalenceOfConditions A D E K hK).equivalence.inverse ⋙
    perfectModuleInclusion A D Set.univ
  let a := (kernelMoritaPerfInverseActionIso A D E K hK).hom.app X
  have hn := (kernelDerivedCounit A D E K).naturality a
  simp only [Functor.comp_map, Functor.id_map] at hn
  have hc : (kernelMoritaPerfInverseIso A D E K hK G hG H hH).hom.app X =
      (kernelDerivedUnit A D E K).app (S.obj X) ≫ (kernelDerivedHom A D E K).map a := by
    change (𝟙 _ ≫ (kernelDerivedUnit A D E K).app (S.obj X) ≫
      𝟙 _ ≫ (kernelDerivedHom A D E K).map a) = _
    simp only [Category.id_comp]
  rw [hc, Functor.map_comp, Category.assoc, hn, ← Category.assoc]
  erw [kernelDerived_left_triangle A D E K (S.obj X), Category.id_comp]

end SerrePositivity.DifferentialGraded.Morita
