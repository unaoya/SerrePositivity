module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.DerivedRestriction
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource

/-!
# 導来係数制限と厳密複体の源

## 概要
DAG XIII Construction 2.2.6 の複体の係数制限を、元の通常複体全体の上で比較する。

## 方針
閉零射の nerve の各単体を項別に制限し、中間の解像の augmentation を反転する。

## 規約
任意の環準同型で、係数制限した複体の半自由性を仮定しない。

## 使われ方
M13 の係数制限と忘却の自然比較。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.ComplexLimits

open CategoryTheory HomologicalComplex SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
open CochainComplex HomComplex
open scoped Simplicial

variable {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T)

/-- 閉零射の列を dg nerve に送る操作は項別係数制限と可換。 -/
lemma complexClosedNerve_restriction :
    (nerveMap (complexToClosed T) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion T (Complex T)) ≫
      complexRestrictionNerve f =
    nerveMap (ScalarExtension.restriction f) ≫ nerveMap (complexToClosed S) ≫
      _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion S (Complex S) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro Γ
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext rfl ?_
  apply heq_of_eq
  funext I a b k hI ha hb hk
  have hab : a ≤ b := by
    rw [ha, hb]
    exact I.min'_le _ (I.max'_mem _)
  let X := Γ.obj a
  let Y := Γ.obj b
  let g : X ⟶ Y := Γ.map (homOfLE hab)
  let R := ScalarExtension.restriction f
  have hmap (j : ℤ) :
      ScalarExtension.restrictCochain f (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed T).map g) j) =
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom ((complexToClosed S).map (R.map g)) j := by
    by_cases h : j = 0
    · subst j
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_zero]
      change ScalarExtension.restrictCochain f
          (cycleFromUnit (homComplex T X Y) ((complexToClosed T).map g)).val =
        (cycleFromUnit (homComplex S (R.obj X) (R.obj Y))
          ((complexToClosed S).map (R.map g))).val
      rw [← complexClosedHomEquiv_cochain, ← complexClosedHomEquiv_cochain]
      change Cochain.map (Cochain.ofHom ((closedToComplex T).map ((complexToClosed T).map g)))
          (ModuleCat.restrictScalars f) =
        Cochain.ofHom ((closedToComplex S).map ((complexToClosed S).map (R.map g)))
      rw [complexToClosed_map, complexToClosed_map, Cochain.map_ofHom]
    · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ _ h, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.closedNerveHom_of_ne _ _ h]
      exact Cochain.map_zero X Y j (ModuleCat.restrictScalars f)
  exact hmap k

/-- 導来係数制限と通常複体の係数制限は元の源上で自然同型。 -/
def barrattEcclesRestrictD_sourceIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (complexOrdinaryDerivedSource T ≫ barrattEcclesRestrictD f)
      (nerveMap (ScalarExtension.restriction f) ≫ complexOrdinaryDerivedSource S) := by
  let L := nerveMap (complexToClosed T) ≫ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DifferentialGradedCategories.closedNerveInclusion T (Complex T)
  let R := complexRestrictionNerve f
  let Q := complexSemifreeResolutionInfinity S
  let H := complexSemifreeResolutionAugmentationHomotopy T
  let K := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H L
  let P := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp K (R ≫ Q)
  have he (x : (nerve (Complex T)) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge P x).toTruncated := by
    let y := atVertex L x
    let e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge H y).toTruncated
    let e' := e.map ((truncation 2).map R)
    have h := complexRestrictionNerve_map_quasiIso f e
      (complexSemifreeResolutionAugmentation_edge_quasiIso T y)
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (f := e'.map ((truncation 2).map Q)) ?_).mpr
    · exact complexSemifreeResolutionInfinity_invertsQuasiIso S e' h
    · change (R ≫ Q).app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge K x).edge =
        (R ≫ Q).app (Opposite.op ⦋1⦌) e.edge
      rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.simplicialHomotopyVertexEdge_precomp_edge H L x]
      rfl
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy P he)
  · simp only [L, R, Q, complexOrdinaryDerivedSource, barrattEcclesRestrictD, Category.assoc]
  · change (L ≫ 𝟙 _) ≫ (R ≫ Q) = _
    rw [Category.comp_id, ← Category.assoc, show L ≫ R = _ from complexClosedNerve_restriction f]
    simp only [complexOrdinaryDerivedSource, Q, Category.assoc]

end SerrePositivity.EInfinity.ComplexLimits
