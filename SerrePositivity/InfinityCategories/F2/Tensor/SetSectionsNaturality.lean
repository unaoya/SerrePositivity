module

public import SerrePositivity.InfinityCategories.F2.Tensor.SetSections
public import SerrePositivity.InfinityCategories.Core.LimitConeExtension
public import SerrePositivity.InfinityCategories.Core.TerminalMappingSpace
public import Mathlib.CategoryTheory.Sites.Sieves.Presheaf
public import SerrePositivity.InfinityCategories.F1.Diagrams.KanWeightedUnstraighteningUnit
public import SerrePositivity.InfinityCategories.F1.Diagrams.SimplicialReplacementFunctor
public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.PinchedObjectNaturality

/-!
概要：集合値重みの制限射と、指定した weighted 比較による G8 の写像空間同値。
方針：要素の圏の比較に実射を用い、極限への制限は錐の普遍性から作る。
規約：指定極限錐を受け取る。G8 の自然性全体の四角形は、このファイルでは未証明。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
open HomotopyLimits F2.Presentable MonoidalClosed
namespace SetWeight

variable {I : Type u} [SmallCategory I] {X Y : I ⥤ Type u}

/-- 定値単体的集合の反転は、同じ集合値係数に自然同型。 -/
def coefficientsOppositeIso (P : I ⥤ Type u) :
    coefficients P ≅ (P ⋙ setsToKan) ⋙ kanObjectOpFunctor ⋙ kanObjectForget :=
  NatIso.ofComponents (fun _ => NatIso.ofComponents (fun _ => Iso.refl _) (by
    intros; rfl)) (by intros; rfl)

def coefficientsOppositeWeightedIso (P : I ⥤ Type u) :
    weightedNerve (coefficients P) ≅
      weightedNerve ((P ⋙ setsToKan) ⋙ kanObjectOpFunctor ⋙ kanObjectForget) :=
  (Over.forget (nerve I)).mapIso
    ((weightedNerveFunctor I).mapIso (coefficientsOppositeIso P))

/-- 元のラベルを、反転係数の指定された coslice 比較へ写す。
底上の同値の無指定な選択を介さず、weighted 比較の実射を使う。 -/
def elementsComparisonNatural (P : I ⥤ Type u) :
    nerve P.Elements ⟶ smallLeftUnstraightening (spaceDiagram P) :=
  elementsToReplacement P ≫ tautScaffold (coefficients P) ≫
    (coefficientsOppositeWeightedIso P).hom ≫
      smallReversedWeightedKanUnstraighteningComparison (P ⋙ setsToKan)

lemma elementsComparisonNatural_projection (P : I ⥤ Type u) :
    elementsComparisonNatural P ≫ smallLeftUnstraighteningProjection (spaceDiagram P) =
      projection P := by
  simp only [elementsComparisonNatural, Category.assoc,
    smallReversedWeightedKanUnstraighteningComparison_projection]
  have h : (coefficientsOppositeWeightedIso P).hom ≫
      weightedNerveProjection ((P ⋙ setsToKan) ⋙ kanObjectOpFunctor ⋙ kanObjectForget) =
      weightedNerveProjection (coefficients P) :=
    ((weightedNerveFunctor I).mapIso (coefficientsOppositeIso P)).hom.w
  rw [h, tautScaffold_projection, elementsToReplacement_projection]

lemma elementsComparisonNatural_isPrecompositionEquivalence (P : I ⥤ Type u) :
    IsPrecompositionEquivalence (elementsComparisonNatural P) := by
  let : ∀ i, KanComplex
      (((P ⋙ setsToKan) ⋙ kanObjectOpFunctor ⋙ kanObjectForget).obj i) :=
    fun i => (kanObjectOpFunctor.obj (setsToKan.obj (P.obj i))).isKanComplex
  have hb := smallLeftUnstraighteningLift_isPrecompositionEquivalence
    (kanDiagramCoherentNerve (P ⋙ setsToKan))
    (weightedNerveProjection ((P ⋙ setsToKan) ⋙ kanObjectOpFunctor ⋙ kanObjectForget))
    (reversedWeightedKanUnstraighteningComparison (P ⋙ setsToKan))
    (reversedWeightedKanUnstraighteningComparison_projection (P ⋙ setsToKan))
    (reversedWeightedKanUnstraighteningComparison_isPrecompositionEquivalence (P ⋙ setsToKan))
  exact (isPrecompositionEquivalence_of_iso (asIso (elementsToReplacement P))).comp
    ((tautScaffold_isPrecompositionEquivalence (coefficients P)).comp
      ((isPrecompositionEquivalence_of_iso (coefficientsOppositeWeightedIso P)).comp hb))

/-- P を始域とする変換の空間を、P.Elements 上の同じ図式の切断空間に移す。 -/
def sectionsEquivalenceNatural (P : I ⥤ Type u)
    (G : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ SpaceInfinity.{u}) :
    QCatEquivalence (pinchedHom (functorVertex (spaceDiagram P)) (functorVertex G))
      ((SSet.uliftFunctor.{u + 1, u}).obj (coherentSpaceSectionsObject (diagram P G)).obj) := by
  let X := spaceDiagram P
  let p := projection P
  let q := smallLeftUnstraighteningProjection G
  let q' := smallLeftUnstraighteningProjection (diagram P G)
  have : ∀ n, Small.{u} (((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)).obj n) :=
    fun n => inferInstanceAs (Small.{u} (ULift.{u + 1} ((nerve I).obj n)))
  let e₀ := (small_leftUnstraighteningPinchedMappingSpaceMap_isQCatEquivalence X G).choose
  let e₁ := (smallLeftUnstraighteningRelativeFunctorIso X G).symm
  let j : Over.mk p ⟶ Over.mk (smallLeftUnstraighteningProjection X) :=
    Over.homMk (elementsComparisonNatural P) (elementsComparisonNatural_projection P)
  have hj := relativeFunctorOverPre_isQCatEquivalence q j
    (elementsComparisonNatural_isPrecompositionEquivalence P)
  let bp : Over.mk q' ≅ Over.mk (pullback.snd q p) :=
    Over.isoMk (smallLeftUnstraighteningBaseChangeIso G p)
      (smallLeftUnstraighteningBaseChangeIso_hom_snd G p)
  let e₂ : relativeFunctorSpace q p ≅ simplicialSections q' :=
    (pullbackSectionsRelativeIso q p).symm ≪≫ simplicialSectionsRelativeIso _ ≪≫
      relativeFunctorOverIso (Iso.refl (Over.mk (𝟙 _))) bp.symm ≪≫
        (simplicialSectionsRelativeIso q').symm
  exact e₀.trans ((qCatEquivalenceOfIso e₁).trans
    (hj.ulift.choose.trans (qCatEquivalenceOfIso ((SSet.uliftFunctor.{u + 1, u}).mapIso e₂))))

/-- 集合値前層 P で重み付けたテンソルからの写像空間。
右辺には、呼び出し側が指定した元の圏上の極限錐そのものを使う。 -/
def tensorSpaceFunctor_setWeightHomNatural (P : I ⥤ Type u)
    {E : SSet.{u + 1}} [Quasicategory E] (hE : F2.Presentable.IsPresentable E) (M : E _⦋0⦌)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)
    (c : JoinCone (diagram P F)) (hc : IsLimitCone c) :
    QCatEquivalence
      (pinchedHom (functorVertex (spaceDiagram P ≫ tensorSpaceFunctor hE M)) (functorVertex F))
      (pinchedHom M c.vertex) := by
  let t := spaceTensorData hE M
  let g := diagram P (F ≫ t.hom)
  have hg : IsLimitCone (mapJoinCone t.hom c) :=
    mapJoinCone_isLimit_of_adjunction t.adjunction c hc
  let e := limitVertexIso (coherentDiagramSectionsCone g) (mapJoinCone t.hom c)
    (coherentDiagramSectionsCone_isLimit g) hg
  have ev : VertexIso (coherentSpaceSectionsVertex g) (t.hom.app _ c.vertex) := by
    rw [← coherentDiagramSectionsCone_vertex g]
    exact e
  letI : KanComplex (simplicialSections (smallLeftUnstraighteningProjection g)) :=
    (coherentSpaceSectionsObject g).isKanComplex
  let vs := spaceValueEquivalence ev
  let hs := (qCatEquivalenceOfIso (eqToIso (coherentSpaceSectionsVertex_object g))).symm.trans vs
  exact (tensorSpaceFunctor_diagramHom hE M (spaceDiagram P) F).trans
    ((sectionsEquivalenceNatural P (F ≫ t.hom)).trans (hs.isQCatEquivalence.ulift.choose.trans
      ((spaceUniverseValueEquivalence (t.hom.app _ c.vertex)).trans
        ((spaceValueEquivalence (t.represents.app (ULift.up c.vertex))).symm.trans
          (covariantRepresentableValueEquivalence M c.vertex)))))


/-- 集合値の射を離散 Kan 値係数の射として使う。 -/
def coefficientsMap (φ : X ⟶ Y) : coefficients X ⟶ coefficients Y :=
  Functor.whiskerRight (Functor.whiskerRight φ setsToKan) kanObjectForget

/-- 元の圏と simplicial replacement のラベル比較は重みの射に自然。 -/
lemma elementsToReplacement_naturality (φ : X ⟶ Y) :
    nerveMap φ.mapElements ≫ elementsToReplacement Y =
      elementsToReplacement X ≫ simplicialReplacementMap (coefficientsMap φ) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  refine Sigma.ext rfl ?_
  apply heq_of_eq
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro t
  rfl

/-- weighted nerve へのラベル比較も同じ係数射に自然。 -/
lemma elementsWeighted_naturality (φ : X ⟶ Y) :
    nerveMap φ.mapElements ≫ elementsToReplacement Y ≫ tautScaffold (coefficients Y) =
      (elementsToReplacement X ≫ tautScaffold (coefficients X)) ≫
        weightedNerveMap (coefficientsMap φ) := by
  rw [← Category.assoc, elementsToReplacement_naturality, Category.assoc,
    tautScaffold_map, ← Category.assoc]

/-- 重みの射を coherent な空間値図式間の辺へ写す。 -/
def spaceDiagramEdge (φ : X ⟶ Y) :
    SSet.Edge (functorVertex (spaceDiagram X)) (functorVertex (spaceDiagram Y)) :=
  kanDiagramNaturalTransformationEdge
    (F := ⟨X ⋙ setsToKan, trivial⟩) (G := ⟨Y ⋙ setsToKan, trivial⟩) (coefficientsMap φ)

/-- 重みの射にテンソルを後合成した、前層の圏の辺。 -/
def tensorWeightEdge {E : SSet.{u + 1}} [Quasicategory E]
    (hE : F2.Presentable.IsPresentable E) (M : E _⦋0⦌) (φ : X ⟶ Y) :
    SSet.Edge (functorVertex (spaceDiagram X ≫ tensorSpaceFunctor hE M))
      (functorVertex (spaceDiagram Y ≫ tensorSpaceFunctor hE M)) :=
  (spaceDiagramEdge φ).map
    ((ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))).map (tensorSpaceFunctor hE M))

/-- G8 の随伴比較は、重みの射による前合成に自然。 -/
def tensorSpaceFunctor_diagramHom_weight_naturality
    {E : SSet.{u + 1}} [Quasicategory E] (hE : F2.Presentable.IsPresentable E)
    (M : E _⦋0⦌) (φ : X ⟶ Y)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E) :
    FunctorIso
      (PinchedInterval.precompose (functorVertex F)
        (Truncated.HomotopyCategory.homMk (tensorWeightEdge hE M φ).toTruncated) ≫
          (tensorSpaceFunctor_diagramHom hE M (spaceDiagram X) F).hom)
      ((tensorSpaceFunctor_diagramHom hE M (spaceDiagram Y) F).hom ≫
        PinchedInterval.precompose (functorVertex (F ≫ (spaceTensorData hE M).hom))
          (Truncated.HomotopyCategory.homMk (spaceDiagramEdge φ).toTruncated)) := by
  exact (postcompositionAdjunction (spaceTensorData hE M).adjunction
    ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I))).pinchedMapNaturalityLeftIso
      (functorVertex F) (Truncated.HomotopyCategory.homMk (spaceDiagramEdge φ).toTruncated)

/-- 重みの射が元の圏の脈体に誘導する射。 -/
def elementsMap (φ : X ⟶ Y) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve X.Elements) ⟶
      (SSet.uliftFunctor.{u + 1, u}).obj (nerve Y.Elements) :=
  (SSet.uliftFunctor.{u + 1, u}).map (nerveMap φ.mapElements)

variable {E : SSet.{u + 1}}
  (φ : X ⟶ Y) (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve I) ⟶ E)

/-- 元の圏の関手は、係数図式への射影を保つ。 -/
lemma elementsMap_diagram : elementsMap φ ≫ diagram Y F = diagram X F := by
  dsimp [elementsMap, diagram, projection]
  rw [← Category.assoc, ← Functor.map_comp]
  have h : nerveMap φ.mapElements ≫ nerveMap (Functor.Elements.π Y) =
      nerveMap (Functor.Elements.π X) := by
    change nerveMap (φ.mapElements ⋙ Functor.Elements.π Y) = _
    rw [NatTrans.mapElements_comp_π]
  rw [h]

/-- 重みの射に沿って制限した錐。 -/
def restrictSectionsCone (c : JoinCone (diagram Y F)) : JoinCone (diagram X F) :=
  ⟨(restrictJoinCone c (elementsMap φ)).val,
    (restrictJoinCone c (elementsMap φ)).property.trans (elementsMap_diagram φ F)⟩

/-- 錐の制限は頂点を変えない。 -/
lemma restrictSectionsCone_vertex (c : JoinCone (diagram Y F)) :
    (restrictSectionsCone φ F c).vertex = c.vertex :=
  restrictJoinCone_vertex c (elementsMap φ)

/-- 制限した錐から指定された極限錐への普遍辺。 -/
def sectionsConeMap (cX : JoinCone (diagram X F)) (hcX : IsLimitCone cX)
    (cY : JoinCone (diagram Y F)) :
    SSet.Edge (X := sliceOver (diagram X F)) (restrictSectionsCone φ F cY) cX :=
  SSet.Edge.ofTruncated (Classical.choice
    ((show IsTerminalVertex (X := sliceOver (diagram X F)) cX from hcX).nonempty_edge
      (restrictSectionsCone φ F cY)))

/-- 切断への制限。向きは Γ(Y,F) → Γ(X,F)。 -/
def sectionsMap (cX : JoinCone (diagram X F)) (hcX : IsLimitCone cX)
    (cY : JoinCone (diagram Y F)) (_hcY : IsLimitCone cY) :
    SSet.Edge cY.vertex cX.vertex := by
  have e := (sectionsConeMap φ F cX hcX cY).map (sliceOverProjection (diagram X F))
  change SSet.Edge (restrictSectionsCone φ F cY).vertex cX.vertex at e
  rw [restrictSectionsCone_vertex] at e
  exact e

/-- 普遍辺のホモトピー類は錐の圏で一意。 -/
lemma sectionsConeMap_homMk_unique [Quasicategory E]
    (cX : JoinCone (diagram X F)) (hcX : IsLimitCone cX)
    (cY : JoinCone (diagram Y F))
    (e : SSet.Edge (X := sliceOver (diagram X F)) (restrictSectionsCone φ F cY) cX) :
    Truncated.HomotopyCategory.homMk (sectionsConeMap φ F cX hcX cY).toTruncated =
      Truncated.HomotopyCategory.homMk e.toTruncated :=
  (show IsTerminalVertex (X := sliceOver (diagram X F)) cX from hcX).isTerminalHo.hom_ext _ _

/-- 極限の存在証明から選んだ錐を使う切断の制限。 -/
def sectionsMapOfHasLimit (hX : HasLimit (diagram X F)) (hY : HasLimit (diagram Y F)) :
    SSet.Edge hY.choose.vertex hX.choose.vertex :=
  sectionsMap φ F hX.choose hX.choose_spec hY.choose hY.choose_spec

/-- BS の篩包含 S ↪ h_U に沿う切断の制限。 -/
def sieveSectionsMap {C : Type u} [SmallCategory C] {U : C} (S : Sieve U)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve Cᵒᵖ) ⟶ E)
    (cS : JoinCone (diagram S.functor F)) (hcS : IsLimitCone cS)
    (cU : JoinCone (diagram (yoneda.obj U) F)) (hcU : IsLimitCone cU) :
    SSet.Edge cU.vertex cS.vertex :=
  sectionsMap S.functorInclusion F cS hcS cU hcU

/-- BS の S4 の生成辺に使う篩包含へのテンソル。 -/
def sieveTensorEdge {C : Type u} [SmallCategory C] {U : C} (S : Sieve U)
    [Quasicategory E] (hE : F2.Presentable.IsPresentable E) (M : E _⦋0⦌) :
    SSet.Edge (functorVertex (spaceDiagram S.functor ≫ tensorSpaceFunctor hE M))
      (functorVertex (spaceDiagram (yoneda.obj U) ≫ tensorSpaceFunctor hE M)) :=
  tensorWeightEdge hE M S.functorInclusion

end SetWeight
end SerrePositivity.InfinityCategories
