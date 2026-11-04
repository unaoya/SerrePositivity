module

public import SerrePositivity.InfinityCategories.F2.Tensor.SetSectionsNaturality
public import SerrePositivity.InfinityCategories.HomotopyLimits.NormalizedConeRestrictionComparison
public import SerrePositivity.InfinityCategories.HomotopyLimits.FixedApexLimitCriterion
public import SerrePositivity.InfinityCategories.F1.Coherent.KanInvertible

/-!
概要：切断制限の自然性を、固定頂点の錐の族と極限の一意性へ帰着する補助。
方針：制限の共通模型を固定し、極限錐の比較同値で全パラメータの同型を反映する。
規約：G8 の四角形そのものはまだ主張しない。頂点ごとの一致には弱めない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits
namespace SetWeight

/-- 極限頂点の標準同型の順射は、錐の圏で指定した任意の普遍辺の射影の類。
頂点の同型だけを比較せず、錐全体の終対象性を使う。 -/
lemma limitVertexIso_hom_eq_coneEdge
    {K E : SSet.{u}} [Quasicategory E] {p : K ⟶ E}
    (c d : JoinCone p) (hc : IsLimitCone c) (hd : IsLimitCone d)
    (e : SSet.Edge (X := sliceOver p) c d) :
    (limitVertexIso c d hc hd).hom =
      Truncated.HomotopyCategory.homMk (e.map (sliceOverProjection p)).toTruncated := by
  have h : (limitConeIso c d hc hd).hom =
      Truncated.HomotopyCategory.homMk e.toTruncated :=
    (show IsTerminalVertex (X := sliceOver p) d from hd).isTerminalHo.hom_ext _ _
  change (hoFunctor.map (sliceOverProjection p)).toFunctor.map
    (limitConeIso c d hc hd).hom = _
  rw [h]
  rfl

/-- 極限への写像の族を、両端固定の錐の族へ写す比較。 -/
def limitConeEndpointComparison {K E : SSet.{u}} [Quasicategory E]
    {p : K ⟶ E} (c : JoinCone p) (x : E _⦋0⦌) :
    pinchedHom x c.vertex ⟶ fixedEndpointConeSpace p x :=
  fixedApexConeHomComparison c x ≫ (fixedApexEndpointConeSpaceIso p x).hom

/-- 指定錐の極限性により、錐の族への比較は全写像空間の同値となる。 -/
lemma limitConeEndpointComparison_isQCatEquivalence
    {K E : SSet.{u}} [Quasicategory E] {p : K ⟶ E}
    (c : JoinCone p) (hc : IsLimitCone c) (x : E _⦋0⦌) :
    IsQCatEquivalence (limitConeEndpointComparison c x) :=
  ((isLimitCone_iff_fixedApexConeHomComparison_homotopyEquivalence c).mp hc x
    ).isQCatEquivalence.comp
      (qCatEquivalenceOfIso (fixedApexEndpointConeSpaceIso p x)).isQCatEquivalence

/-- 錐の族として同型な二つの写像の族は、極限への写像の族として同型。
パラメータ A 全体を保持し、各頂点での射の一意性だけには帰着しない。 -/
def limitConeMapIsoOfConeFamilyIso {A K E : SSet.{u}} [Quasicategory E]
    {p : K ⟶ E} (c : JoinCone p) (hc : IsLimitCone c) (x : E _⦋0⦌)
    (a b : A ⟶ pinchedHom x c.vertex)
    (h : FunctorIso (a ≫ limitConeEndpointComparison c x)
      (b ≫ limitConeEndpointComparison c x)) : FunctorIso a b := by
  let e := (limitConeEndpointComparison_isQCatEquivalence c hc x).choose
  have he : e.hom = limitConeEndpointComparison c x := rfl
  have ha : FunctorIso (a ≫ limitConeEndpointComparison c x ≫ e.inv) a := by
    simpa only [Category.assoc, Category.comp_id, he] using e.homInvIso.precomp a
  have hb : FunctorIso (b ≫ limitConeEndpointComparison c x ≫ e.inv) b := by
    simpa only [Category.assoc, Category.comp_id, he] using e.homInvIso.precomp b
  have hab : FunctorIso (a ≫ limitConeEndpointComparison c x ≫ e.inv)
      (b ≫ limitConeEndpointComparison c x ≫ e.inv) := by
    simpa only [Category.assoc] using h.postcomp e.inv
  exact ha.symm ≪≫ hab ≪≫ hb

/-- 錐の族の同型から、空間のホモトピー圏での写像の等式を得る。 -/
lemma limitConeMap_homMk_eq_of_coneFamilyIso
    {A K E : SSet.{u}} [KanComplex A] [Quasicategory E]
    {p : K ⟶ E} (c : JoinCone p) (hc : IsLimitCone c) (x : E _⦋0⦌)
    (a b : A ⟶ pinchedHom x c.vertex)
    (h : FunctorIso (a ≫ limitConeEndpointComparison c x)
      (b ≫ limitConeEndpointComparison c x)) :
    Truncated.HomotopyCategory.homMk
      (coherentNerveEdge (C := KanObject.{u})
        (X := ⟨A, inferInstance⟩) (Y := ⟨pinchedHom x c.vertex, inferInstance⟩) a).toTruncated =
    Truncated.HomotopyCategory.homMk
      (coherentNerveEdge (C := KanObject.{u})
        (X := ⟨A, inferInstance⟩) (Y := ⟨pinchedHom x c.vertex, inferInstance⟩) b).toTruncated := by
  exact coherentKanEdge_homMk_eq_of_functorIso
    (K := ⟨A, inferInstance⟩) (L := ⟨pinchedHom x c.vertex, inferInstance⟩)
    (limitConeMapIsoOfConeFamilyIso c hc x a b h)

variable {I : Type u} [SmallCategory I] {X Y : I ⥤ Type u}
  {E : SSet.{u + 1}}
  (φ : X ⟶ Y) (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)

/-- 要素の圏に沿う制限を、頂点と図式を固定した錐の族へ移す。 -/
def sectionsConeFamilyRestriction (x : E _⦋0⦌) :
    fixedEndpointConeSpace (diagram Y F) x ⟶ fixedEndpointConeSpace (diagram X F) x :=
  normalizedEndpointConeRestriction (diagram Y F) (diagram X F) (elementsMap φ)
    (elementsMap_diagram φ F) x

/-- 切断の制限と錐の族への比較は、全パラメータで厳密に可換。 -/
lemma sectionsConeFamilyRestriction_fromSections (x : E _⦋0⦌) :
    (relativeFunctorPre (sliceUnderProjection (SSet.yonedaEquiv.symm x))
        (diagram Y F) (elementsMap φ) ≫
      eqToHom (congrArg (fun r => coherentConeSectionSpace r x)
        (elementsMap_diagram φ F))) ≫
        sectionEndpointConeComparison (diagram X F) x =
      sectionEndpointConeComparison (diagram Y F) x ≫
        sectionsConeFamilyRestriction φ F x :=
  normalizedSectionEndpointComparison_restrict (diagram Y F) (diagram X F)
    (elementsMap φ) (elementsMap_diagram φ F) x

end SetWeight
end SerrePositivity.InfinityCategories
