module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Sheaves.NativeLeftSectionsApexMap
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsNativeGlobalApex
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsOriginalNativeFactor
public import SerrePositivity.InfinityCategories.Sheaves.DiscreteWeightedMovingIndex
public import SerrePositivity.InfinityCategories.Sheaves.NativeRightKanDensityComposition
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEdgeNaturality

/-!
概要：元の切断関手の辺を指定した極限錐の間の射で計算する。
方針：大域右 Kan 比較の自然性と固定形状同型に沿う極限の比較を合成する。
  文献対応：HTT 5.1.5.6（双対）。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

namespace SerrePositivity.InfinityCategories.Sheaves

private lemma compArrow {T : Type u} [Category.{u} T] {a b c x y z : T}
    (f : a ⟶ b) (g : b ⟶ c) (F : x ⟶ y) (G : y ⟶ z)
    (hf : Arrow.mk f = Arrow.mk F) (hg : Arrow.mk g = Arrow.mk G) :
    Arrow.mk (f ≫ g) = Arrow.mk (F ≫ G) := by
  obtain ⟨ha, hb, hf⟩ := (Arrow.mk_eq_mk_iff _ _).1 hf
  obtain ⟨_, hc, hg⟩ := (Arrow.mk_eq_mk_iff _ _).1 hg
  subst a b c
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hf hg
  rw [hf, hg]

private lemma hom_comp_of_normalized {T : Type u} [Category T] {a b x y : T}
    (f : a ⟶ b) (g : x ⟶ y) (h₀ : a = x) (h₁ : b = y)
    (h : eqToHom h₀.symm ≫ f ≫ eqToHom h₁ = g) :
    f ≫ eqToHom h₁ = eqToHom h₀ ≫ g := by
  subst x y
  simpa only [eqToHom_refl, Category.id_comp] using h

private lemma sliceHom_cast_arrow
    {J K E : SSet.{u}} {p p' : J ⟶ E} {q q' : K ⟶ E}
    (hp : p = p') (hq : q = q') (a : J ⟶ K)
    (h : a ≫ q = p) (h' : a ≫ q' = p')
    (c : JoinCone p) (d : JoinCone q)
    (k : (HomotopyCategory.mk ((restrictJoinCone d a).cast h) : hoFunctor.obj (sliceOver p)) ⟶
      HomotopyCategory.mk c) :
    ∃ s : (HomotopyCategory.mk ((restrictJoinCone (d.cast hq) a).cast h') :
      hoFunctor.obj (sliceOver p')) ⟶ HomotopyCategory.mk (c.cast hp),
      Arrow.mk ((hoFunctor.map (sliceOverProjection p')).toFunctor.map s) =
        Arrow.mk ((hoFunctor.map (sliceOverProjection p)).toFunctor.map k) := by
  subst p' q'
  exact ⟨k, rfl⟩

private lemma globalComparison_mapArrow
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (W : (PresheafCat C SpaceInfinity.{u}).op ⟶ E)
    (G : (PresheafInfinity (nerve C)).op ⟶ E)
    (m : FunctorHom W ((SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).inv ≫ G))
    {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q) :
    let x := SSet.opObjEquiv.symm (functorVertex (discretePresheaf Q))
    let y := SSet.opObjEquiv.symm (functorVertex (discretePresheaf P))
    let n := (SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).inv
    let f := SSet.Edge.ofTruncated (X := (PresheafCat C SpaceInfinity.{u}).op)
      (edgeOp (normalizedDiscreteEdge φ).toTruncated)
    let e := SSet.Edge.ofTruncated (X := (PresheafInfinity (nerve C)).op)
      (edgeOp (nativeDiscreteEdge φ).toTruncated)
    Arrow.mk (Truncated.HomotopyCategory.homMk (f.map W).toTruncated ≫ functorHomEvaluate m y) =
      Arrow.mk (functorHomEvaluate m x ≫ Truncated.HomotopyCategory.homMk (e.map G).toTruncated) := by
  intro x y n f e
  have H := functorHomEvaluate_edge_naturality m f
  have he : Arrow.mk (Truncated.HomotopyCategory.homMk (f.map (n ≫ G)).toTruncated) =
      Arrow.mk (Truncated.HomotopyCategory.homMk (e.map G).toTruncated) := by
    apply Truncated.HomotopyCategory.congr_arrowMk_homMk
    change G.app (Opposite.op ⦋1⦌) (n.app _ f.edge) = G.app _ e.edge
    congr 1
  exact (congrArg Arrow.mk H).trans (compArrow _ _ _ _ rfl he)

/-- 元の切断関手の辺を指定した極限錐の間の射で計算する。 -/
@[cite HTT "5.1.5.6" (partial := special) "小さい通常の site の集合値重みの指定比較。"]
lemma weightedSections_originalLeftLimitIso_specifiedMap :
  ∀ {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E],
  ∀ (O : Presheaf C E) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E),
  ∀ {P Q : Cᵒᵖ ⥤ Type u} (φ : P ⟶ Q),
  let U := SSet.uliftFunctor.{u + 1, u}
  let a := U.map (smallUnstraighteningFunctorHom (discretePresheafHom φ))
  let DP := U.map (smallLeftUnstraighteningProjection (discretePresheaf P)) ≫ O
  let DQ := U.map (smallLeftUnstraighteningProjection (discretePresheaf Q)) ≫ O
  ∀ (h : a ≫ DQ = DP) (dP : JoinCone DP) (dQ : JoinCone DQ)
   (hdP : IsLimitCone dP) (hdQ : IsLimitCone dQ),
  let rQ := (restrictJoinCone dQ a).cast h
  ∀ (k : SSet.Edge (X := sliceOver DP) rQ dP),
  let k₀ := eqToHom (congrArg HomotopyCategory.mk
   ((JoinCone.vertex_cast _ h).trans (restrictJoinCone_vertex dQ a)).symm) ≫
   Truncated.HomotopyCategory.homMk (k.map (sliceOverProjection DP)).toTruncated
  let b := ((nerve.edgeMk φ).map (discretePresheafInclusion C).val).toTruncated
  let r := (edgeOp b).map ((truncation 2).map (weightedSections O hE))
  let F := fun v => (weightedSections O hE).app _ (opObjEquiv.symm v)
  let cP := eqToHom (congrArg HomotopyCategory.mk
   (congrArg F ((discretePresheafInclusion C).property.1 P)))
  let cQ := eqToHom (congrArg HomotopyCategory.mk
   (congrArg F ((discretePresheafInclusion C).property.1 Q)))
  Truncated.HomotopyCategory.homMk r ≫ cP ≫
     (weightedSections_originalLeftLimitIso O hE (discretePresheaf P) dP hdP).hom =
  cQ ≫ (weightedSections_originalLeftLimitIso O hE (discretePresheaf Q) dQ hdQ).hom ≫ k₀ := by
  intro C hC E hQC O hE P Q φ U a DP DQ h dP dQ hdP hdQ rQ k k₀ b r F cP cQ
  let i := nerveOppositeIso (C := C)
  let j := fixedYonedaDomainIso C
  let w := (SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).symm
  let O' := j.inv ≫ O
  let N (Z : Cᵒᵖ ⥤ Type u) := U.map i.hom ≫ discretePresheaf Z
  let f (Z : Cᵒᵖ ⥤ Type u) := U.mapIso (smallLeftUnstraighteningBaseIso i (discretePresheaf Z))
  let p (Z : Cᵒᵖ ⥤ Type u) := U.map (smallLeftUnstraighteningProjection (N Z)) ≫ U.map i.hom
  let q (Z : Cᵒᵖ ⥤ Type u) := U.map (smallLeftUnstraighteningProjection (discretePresheaf Z))
  let m := smallUnstraighteningFunctorHom (discretePresheafHom φ)
  let aN := U.map ((smallLeftUnstraighteningBaseIso i (discretePresheaf P)).hom ≫ m ≫
    (smallLeftUnstraighteningBaseIso i (discretePresheaf Q)).inv)
  have hf (Z : Cᵒᵖ ⥤ Type u) : (f Z).hom ≫ q Z = p Z := by
    change U.map (smallLeftUnstraighteningBaseIso i (discretePresheaf Z)).hom ≫
      U.map (smallLeftUnstraighteningProjection (discretePresheaf Z)) = _
    rw [← U.map_comp, smallLeftUnstraighteningBaseIso_projection, U.map_comp]
  have hcomm : aN ≫ (f Q).hom = (f P).hom ≫ a := by
    let FP := smallLeftUnstraighteningBaseIso i (discretePresheaf P)
    let FQ := smallLeftUnstraighteningBaseIso i (discretePresheaf Q)
    change U.map (FP.hom ≫ m ≫ FQ.inv) ≫ U.map FQ.hom = U.map FP.hom ≫ U.map m
    rw [← U.map_comp, ← U.map_comp]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have ha : a ≫ q Q = q P := by
    change U.map m ≫ U.map (smallLeftUnstraighteningProjection (discretePresheaf Q)) = _
    rw [← U.map_comp, smallUnstraighteningFunctorHom_projection]
  have haN : aN ≫ p Q = p P := by
    rw [← hf Q, ← Category.assoc, hcomm, Category.assoc, ha, hf P]
  have hcoef (Z : Cᵒᵖ ⥤ Type u) : p Z ≫ O = nativeLeftSectionsDiagram (N Z) O' := by
    have hi : (uliftOppositeIso (nerve C)).hom ≫ j.inv = U.map i.hom := by
      dsimp only [j, fixedYonedaDomainIso, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv]
      exact Iso.hom_inv_id_assoc _ _
    dsimp only [p, nativeLeftSectionsDiagram, O']
    rw [Category.assoc, ← Category.assoc (uliftOppositeIso (nerve C)).hom j.inv O, hi]
  have haD : aN ≫ nativeLeftSectionsDiagram (N Q) O' =
      nativeLeftSectionsDiagram (N P) O' := by
    rw [← hcoef, ← hcoef, ← Category.assoc, haN]
  let tP := nativeLeftSectionsTransportCone (N P) O' hE
  let tQ := nativeLeftSectionsTransportCone (N Q) O' hE
  let lP := nativeLeftSectionsTransportCone_isLimit (N P) O' hE
  let lQ := nativeLeftSectionsTransportCone_isLimit (N Q) O' hE
  obtain ⟨n₀⟩ := IsTerminalVertex.nonempty_edge
    (X := sliceOver (nativeLeftSectionsDiagram (N P) O')) lP ((restrictJoinCone tQ aN).cast haD)
  let n := Truncated.HomotopyCategory.homMk n₀
  let hD : aN ≫ (p Q ≫ O) = p P ≫ O := by rw [← Category.assoc, haN]
  obtain ⟨s, hs⟩ := sliceHom_cast_arrow (hcoef P).symm (hcoef Q).symm aN haD hD tP tQ n
  let e := SSet.Edge.ofTruncated (X := (PresheafInfinity (nerve C)).op)
    (edgeOp (nativeDiscreteEdge φ).toTruncated)
  let δ := SSet.opFunctor.map (yonedaInfinityMap (nerve C))
  have hprojN : aN ≫ U.map (smallLeftUnstraighteningProjection (N Q)) =
      U.map (smallLeftUnstraighteningProjection (N P)) := by
    apply (cancel_mono (U.map i.hom)).mp
    exact (Category.assoc _ _ _).trans haN
  have hj : (aN ≫ leftElementsRightKanComparison (N Q)) ≫
        rightKanProjection δ (SSet.opObjEquiv.symm (functorVertex (N Q))) =
      leftElementsRightKanComparison (N P) ≫
        rightKanProjection δ (SSet.opObjEquiv.symm (functorVertex (N P))) := by
    have h0 := leftElementsRightKanComparison_projection (N Q)
    have h1 := leftElementsRightKanComparison_projection (N P)
    refine (Category.assoc _ _ _).trans ((congrArg (aN ≫ ·) h0).trans ?_)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (uliftOppositeIso (nerve C)).hom) hprojN).trans h1.symm)
  have hface := discreteWeightedSectionsMovingIndex_actual φ
    e.δ_one_yonedaEquiv_symm e.δ_zero_yonedaEquiv_symm
  let G := nativeWeightedSections O' hE
  let ν := Truncated.HomotopyCategory.homMk (e.map G).toTruncated
  have hn := nativeLeftSectionsTransport_apexMap O' hE e aN hj hface haD n
  have hν := hs.trans hn.symm
  let c (Z : Cᵒᵖ ⥤ Type u) := (nativeLeftSectionsTransportCone (N Z) O' hE).cast (hcoef Z).symm
  let hc (Z : Cᵒᵖ ⥤ Type u) := (nativeLeftSectionsTransportCone_isLimit (N Z) O' hE).cast (hcoef Z).symm
  let lp := limitVertexIsoOfOverEquivalence (f P).hom
    (isPrecompositionEquivalence_of_iso (f P)).isQCatEquivalence (hf P) O (c P) dP (hc P) hdP
  let lq := limitVertexIsoOfOverEquivalence (f Q).hom
    (isPrecompositionEquivalence_of_iso (f Q)).isQCatEquivalence (hf Q) O (c Q) dQ (hc Q) hdQ
  let J : VertexIso
      (relativeFunctorVertex (q Q) (p P) (aN ≫ (f Q).hom) (by rw [Category.assoc, hf, haN]))
      (relativeFunctorVertex (q Q) (p P) ((f P).hom ≫ a) (by rw [Category.assoc, ha, hf])) :=
    eqToIso (congrArg HomotopyCategory.mk (Subtype.ext (congrArg functorVertex hcomm)))
  have hsquare := limitVertexIso_restrictionSquare (p P) (p Q) (q P) (q Q)
    aN a (f P).hom (f Q).hom haN ha (hf P) (hf Q)
    (isPrecompositionEquivalence_of_iso (f P)).isQCatEquivalence
    (isPrecompositionEquivalence_of_iso (f Q)).isQCatEquivalence J O
    (c P) (c Q) dP dQ (hc P) (hc Q) hdP hdQ s
    (Truncated.HomotopyCategory.homMk k.toTruncated)
  let α := (nativeWeightedSectionsData O' hE).2.val
  let hα := nativeWeightedSections_isRightKanExtension O' hE
  have hO : j.hom ≫ O' = O := by dsimp only [O']; rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  let H := nativeSetShapeOppositeYoneda_square C
  let β := rightKanCounitIsoSquare j w H α
  let hβ := kanRightKanExtension_of_isoSquare j w H α hα
  let β' : SSet.Homotopy (nativeSetShapeOppositeYoneda C ≫ (w.hom ≫ G)) O := hO ▸ β
  have hβ' : IsRightKanExtension (nativeSetShapeOppositeYoneda C) O (w.hom ≫ G) β' := by
    have aux : ∀ (X Y : Presheaf C E) (hXY : X = Y)
        (β₀ : SSet.Homotopy (nativeSetShapeOppositeYoneda C ≫ (w.hom ≫ G)) X),
        IsRightKanExtension (nativeSetShapeOppositeYoneda C) X (w.hom ≫ G) β₀ →
        IsRightKanExtension (nativeSetShapeOppositeYoneda C) Y (w.hom ≫ G) (hXY ▸ β₀) := by
      intro X Y hXY β₀ hb
      cases hXY
      exact hb
    exact aux _ _ hO β hβ
  let cmp := weightedSections_nativeShape_comparison O hE β' hβ'
  let v (Z : Cᵒᵖ ⥤ Type u) := SSet.opObjEquiv.symm (functorVertex (N Z))
  let v₀ (Z : Cᵒᵖ ⥤ Type u) := SSet.opObjEquiv.symm (functorVertex (discretePresheaf Z))
  let g (Z : Cᵒᵖ ⥤ Type u) := functorHomEvaluate cmp.hom (v₀ Z)
  let hV (Z : Cᵒᵖ ⥤ Type u) : (c Z).vertex = G.app _ (v Z) :=
    (JoinCone.vertex_cast _ (hcoef Z).symm).trans (nativeLeftSectionsTransportCone_vertex (N Z) O' hE)
  let ε (Z : Cᵒᵖ ⥤ Type u) := eqToHom (congrArg HomotopyCategory.mk (hV Z).symm)
  have hval (Z : Cᵒᵖ ⥤ Type u) (d : JoinCone (q Z ≫ O)) (hd : IsLimitCone d) :
      (weightedSections_originalLeftLimitIso O hE (discretePresheaf Z) d hd).hom =
        g Z ≫ ε Z ≫
          (limitVertexIsoOfOverEquivalence (f Z).hom
            (isPrecompositionEquivalence_of_iso (f Z)).isQCatEquivalence (hf Z) O
            (c Z) d (hc Z) hd).hom := by
    let t := nativeWeightedSections_valueTransport O' hE (v Z)
    let ht := nativeWeightedSections_valueTransport_isLimit O' hE (v Z)
    have hA := originalLeftLimitIso_hom_nativeRestriction O hE (discretePresheaf Z)
      (hcoef Z) (hf Z) d hd
    have hB := weightedSections_nativeLimitIso_hom_transportGlobal O hE (v₀ Z) α hα hO t ht
    rw [hA, hB]
    simp only [g, ε, Category.assoc, eqToHom_trans_assoc]
    rfl
  let e₀ := SSet.Edge.ofTruncated (X := (PresheafCat C SpaceInfinity.{u}).op)
    (edgeOp (normalizedDiscreteEdge φ).toTruncated)
  let w₀ := Truncated.HomotopyCategory.homMk (e₀.map (weightedSections O hE)).toTruncated
  let x₀ := congrArg F ((discretePresheafInclusion C).property.1 Q)
  let x₁ := congrArg F ((discretePresheafInclusion C).property.1 P)
  have hRaw : Truncated.HomotopyCategory.homMk r ≫ cP = cQ ≫ w₀ :=
    hom_comp_of_normalized _ _ (congrArg HomotopyCategory.mk x₀)
      (congrArg HomotopyCategory.mk x₁)
      (homMk_transport x₀ x₁ r (e₀.map (weightedSections O hE)).toTruncated rfl)
  have hNat := globalComparison_mapArrow (weightedSections O hE) G cmp.hom φ
  have hN : Arrow.mk (Truncated.HomotopyCategory.homMk r ≫ cP ≫ g P) =
      Arrow.mk (g Q ≫ ν) := by
    calc
      _ = Arrow.mk (cQ ≫ (w₀ ≫ g P)) := by rw [← Category.assoc, hRaw, Category.assoc]
      _ = Arrow.mk (w₀ ≫ g P) := Arrow.arrow_mk_eqToHom_comp _ _
      _ = _ := hNat
  have hSq : Arrow.mk (ν ≫ ε P ≫ lp.hom) = Arrow.mk (ε Q ≫ lq.hom ≫ k₀) := by
    rw [Arrow.arrow_mk_eqToHom_comp]
    have hν' : Arrow.mk (ν ≫ ε P) =
      Arrow.mk (normalizedSliceHom ((JoinCone.vertex_cast _ hD).trans (restrictJoinCone_vertex (c Q) aN)) s) := by
      rw [Arrow.arrow_mk_comp_eqToHom]
      exact hν.symm.trans (Arrow.arrow_mk_eqToHom_comp _ _).symm
    exact ((congrArg Arrow.mk (Category.assoc ν (ε P) lp.hom).symm).trans
      (compArrow _ _ _ _ hν' rfl)).trans (congrArg Arrow.mk hsquare.symm)
  rw [hval P dP hdP, hval Q dQ hdQ]
  change Truncated.HomotopyCategory.homMk r ≫ cP ≫ (g P ≫ ε P ≫ lp.hom) =
    cQ ≫ (g Q ≫ ε Q ≫ lq.hom) ≫ k₀
  apply Arrow.mk_injective
  simp only [Category.assoc]
  calc
    _ = Arrow.mk ((Truncated.HomotopyCategory.homMk r ≫ cP ≫ g P) ≫ (ε P ≫ lp.hom)) := by
      simp only [Category.assoc]
    _ = Arrow.mk ((g Q ≫ ν) ≫ (ε P ≫ lp.hom)) := compArrow _ _ _ _ hN rfl
    _ = Arrow.mk (g Q ≫ (ν ≫ ε P ≫ lp.hom)) := by rw [Category.assoc]
    _ = Arrow.mk (g Q ≫ (ε Q ≫ lq.hom ≫ k₀)) := compArrow _ _ _ _ rfl hSq
    _ = _ := (Arrow.arrow_mk_eqToHom_comp _ _).symm

end SerrePositivity.InfinityCategories.Sheaves
