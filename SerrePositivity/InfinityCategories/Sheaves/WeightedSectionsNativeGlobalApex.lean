module

public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsNativeLimitGlobalComparison
public import SerrePositivity.InfinityCategories.Sheaves.WeightedSectionsNativeLimitComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RightKanShapeIsoData
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.DiagramEqLimitVertexComposition

/-!
概要：元の右 Kan 輸送の極限頂点比較を、固定 Yoneda の形状同型を経由して大域比較の成分へ結ぶ。
方針：指定した辺と添字の座標に既存の評価則を適用する。
使われ方：離散前層の重み付き切断の自然性。
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Sheaves
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

namespace SerrePositivity.InfinityCategories.Sheaves

local instance localShapeProjection {K C : SSet.{u}}
    [Quasicategory C] (δ : K ⟶ C) (v : C _⦋0⦌) :
    LeftFibration (rightKanProjection δ v) :=
  ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p :=
    sliceUnderProjection (SSet.yonedaEquiv.symm v)))⟩

local instance localShapeQuasicategory {K C : SSet.{u}}
    [Quasicategory K] [Quasicategory C] (δ : K ⟶ C) (v : C _⦋0⦌) :
    Quasicategory (rightKanShape δ v) := quasicategory_of_innerFibration (rightKanProjection δ v)

private lemma rightKanLimitVertexIsoOfIsoSquare_hom_source_comp
    {K K' C C' D : SSet.{u}}
    [Quasicategory K] [Quasicategory K'] [Quasicategory C] [Quasicategory C'] [Quasicategory D]
    (a : K ≅ K') (b : C ≅ C') {δ : K ⟶ C} {δ' : K' ⟶ C'}
    (hw : δ ≫ b.hom = a.hom ≫ δ') (O : K' ⟶ D) (v : C _⦋0⦌)
    (c s : JoinCone (rightKanDiagram δ (a.hom ≫ O) v))
    (d : JoinCone (rightKanDiagram δ' O (b.hom.app (Opposite.op ⦋0⦌) v)))
    (hc : IsLimitCone c) (hs : IsLimitCone s) (hd : IsLimitCone d) :
    (limitVertexIso c s hc hs).hom ≫ (rightKanLimitVertexIsoOfIsoSquare a b hw O v s d hs hd).hom =
      (rightKanLimitVertexIsoOfIsoSquare a b hw O v c d hc hd).hom := by
  let i := rightKanShapeIsoOfSquare a b hw v
  let t := restrictJoinCone d i.hom
  have ht := (isLimitCone_iff_restrict_equivalentShape
    i.hom (isPrecompositionEquivalence_of_iso i).isQCatEquivalence d).mp hd
  have he : rightKanDiagram δ (a.hom ≫ O) v =
      i.hom ≫ rightKanDiagram δ' O (b.hom.app (Opposite.op ⦋0⦌) v) := by
    rw [rightKanDiagram, rightKanDiagram, ← Category.assoc]
    change _ = i.hom ≫ _ ≫ O
    rw [← Category.assoc, rightKanShapeIsoOfSquare_projection, Category.assoc]
  change (limitVertexIso c s hc hs).hom ≫
    ((restrictJoinCone_vertex d i.hom) ▸ limitVertexIsoOfDiagramEq he s t hs ht).hom =
      ((restrictJoinCone_vertex d i.hom) ▸ limitVertexIsoOfDiagramEq he c t hc ht).hom
  have hS := vertexIso_transport_target_hom (restrictJoinCone_vertex d i.hom)
    (limitVertexIsoOfDiagramEq he s t hs ht)
  have hC := vertexIso_transport_target_hom (restrictJoinCone_vertex d i.hom)
    (limitVertexIsoOfDiagramEq he c t hc ht)
  rw [hS, hC, ← Category.assoc, limitVertexIso_hom_comp_diagramEq]

private lemma limitVertexIso_hom_of_eq {K D : SSet.{u}} [Quasicategory D] {p : K ⟶ D}
    {c d : JoinCone p} (hc : IsLimitCone c) (hd : IsLimitCone d) (hval : c = d) :
    (limitVertexIso c d hc hd).hom = eqToHom (congrArg (fun z => HomotopyCategory.mk z.vertex) hval) := by
  subst d
  exact limitVertexIso_hom_refl c hc

private lemma rightKanLimitVertexIsoOfIsoSquare_hom_of_restriction
    {K K' C C' D : SSet.{u}}
    [Quasicategory K] [Quasicategory K'] [Quasicategory C] [Quasicategory C'] [Quasicategory D]
    (a : K ≅ K') (b : C ≅ C') {δ : K ⟶ C} {δ' : K' ⟶ C'}
    (hw : δ ≫ b.hom = a.hom ≫ δ') (O : K' ⟶ D) (v : C _⦋0⦌)
    (c : JoinCone (rightKanDiagram δ (a.hom ≫ O) v))
    (d : JoinCone (rightKanDiagram δ' O (b.hom.app (Opposite.op ⦋0⦌) v)))
    (hc : IsLimitCone c) (hd : IsLimitCone d)
    (hval : c.val = (restrictJoinCone d (rightKanShapeIsoOfSquare a b hw v).hom).val)
    (h : c.vertex = d.vertex) :
    (rightKanLimitVertexIsoOfIsoSquare a b hw O v c d hc hd).hom =
      eqToHom (congrArg HomotopyCategory.mk h) := by
  let i := rightKanShapeIsoOfSquare a b hw v
  let t := restrictJoinCone d i.hom
  have ht := (isLimitCone_iff_restrict_equivalentShape
    i.hom (isPrecompositionEquivalence_of_iso i).isQCatEquivalence d).mp hd
  have he : rightKanDiagram δ (a.hom ≫ O) v =
      i.hom ≫ rightKanDiagram δ' O (b.hom.app (Opposite.op ⦋0⦌) v) := by
    rw [rightKanDiagram, rightKanDiagram, ← Category.assoc]
    change _ = i.hom ≫ _ ≫ O
    rw [← Category.assoc, rightKanShapeIsoOfSquare_projection, Category.assoc]
  have hct : c.cast he = t := Subtype.ext (by
    change c.val = t.val
    exact hval)
  change ((restrictJoinCone_vertex d i.hom) ▸ limitVertexIsoOfDiagramEq he c t hc ht).hom = _
  have hC := vertexIso_transport_target_hom (restrictJoinCone_vertex d i.hom)
    (limitVertexIsoOfDiagramEq he c t hc ht)
  rw [hC, limitVertexIsoOfDiagramEq_hom, limitVertexIso_hom_of_eq _ _ hct, eqToHom_trans]

private noncomputable def nativeLimitIsoOfCoefficientEq
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (O O₀ : Presheaf C E) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (h : O₀ = O)
    (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌)
    (s : JoinCone (rightKanDiagram (nativeSetShapeOppositeYoneda C) O₀ P))
    (hs : IsLimitCone s) :
    VertexIso ((weightedSections O hE).app _ P) s.vertex := by
  cases h
  exact weightedSections_nativeShapeLimitIso O hE P s hs

private lemma nativeLimitIsoOfCoefficientEq_hom_comp
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (O O₀ : Presheaf C E) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (h : O₀ = O)
    (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌)
    (s t : JoinCone (rightKanDiagram (nativeSetShapeOppositeYoneda C) O₀ P))
    (hs : IsLimitCone s) (ht : IsLimitCone t) :
    (nativeLimitIsoOfCoefficientEq O O₀ hE h P s hs).hom ≫ (limitVertexIso s t hs ht).hom =
      (nativeLimitIsoOfCoefficientEq O O₀ hE h P t ht).hom := by
  cases h
  exact weightedSections_nativeShapeLimitIso_hom_comp O hE P s t hs ht

private lemma weightedSections_nativeLimitIso_hom_through
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (O : Presheaf C E) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌) :
    let a := fixedYonedaDomainIso C
    let b := (SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).symm
    let O' := a.inv ≫ O
    ∀ (h : a.hom ≫ O' = O)
      (s : JoinCone (rightKanDiagram (nativeSetShapeOppositeYoneda C) (a.hom ≫ O') P))
      (d : JoinCone (rightKanDiagram (SSet.opFunctor.map (yonedaInfinityMap (nerve C))) O'
        (b.hom.app (Opposite.op ⦋0⦌) P)))
      (hs : IsLimitCone s) (hd : IsLimitCone d),
    (weightedSections_nativeLimitIso O hE P d hd).hom =
      (nativeLimitIsoOfCoefficientEq O (a.hom ≫ O') hE h P s hs).hom ≫
        (rightKanLimitVertexIsoOfIsoSquare a b
          (nativeSetShapeOppositeYoneda_square C) O' P s d hs hd).hom := by
  intro a b O' h s d hs hd
  have H (t : JoinCone (rightKanDiagram (nativeSetShapeOppositeYoneda C) (a.hom ≫ O') P))
      (ht : IsLimitCone t) :
      (nativeLimitIsoOfCoefficientEq O (a.hom ≫ O') hE h P t ht).hom ≫
          (rightKanLimitVertexIsoOfIsoSquare a b
            (nativeSetShapeOppositeYoneda_square C) O' P t d ht hd).hom =
        (nativeLimitIsoOfCoefficientEq O (a.hom ≫ O') hE h P s hs).hom ≫
          (rightKanLimitVertexIsoOfIsoSquare a b
            (nativeSetShapeOppositeYoneda_square C) O' P s d hs hd).hom := by
    rw [← rightKanLimitVertexIsoOfIsoSquare_hom_source_comp a b
      (nativeSetShapeOppositeYoneda_square C) O' P t s d ht hs hd,
      ← Category.assoc, nativeLimitIsoOfCoefficientEq_hom_comp]
  unfold weightedSections_nativeLimitIso
  rw [Iso.trans_hom]
  exact H _ _

private lemma nativeLimitIsoOfCoefficientEq_hom_global
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (O O₀ : Presheaf C E) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (h : O₀ = O)
    {G : (PresheafCat C SpaceInfinity.{u}).op ⟶ E}
    (β : SSet.Homotopy (nativeSetShapeOppositeYoneda C ≫ G) O₀)
    (hβ : IsRightKanExtension (nativeSetShapeOppositeYoneda C) O₀ G β)
    (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌)
    (t : RightKanConeTransport (nativeSetShapeOppositeYoneda C) O₀ G β P)
    (ht : IsLimitCone t.cone) :
    let β' : SSet.Homotopy (nativeSetShapeOppositeYoneda C ≫ G) O := h ▸ β
    let hβ' : IsRightKanExtension (nativeSetShapeOppositeYoneda C) O G β' := by
      subst O
      exact hβ
    (nativeLimitIsoOfCoefficientEq O O₀ hE h P t.cone ht).hom =
      functorHomEvaluate (weightedSections_nativeShape_comparison O hE β' hβ').hom P ≫
        eqToHom (congrArg HomotopyCategory.mk t.cone_vertex).symm := by
  subst O₀
  dsimp only [nativeLimitIsoOfCoefficientEq]
  rw [weightedSections_nativeShapeLimitIso_hom_eq_globalComparison O hE β hβ P t ht t.cone ht,
    limitVertexIso_hom_refl, Category.comp_id]

/-- 元の右 Kan 輸送の極限頂点比較を、固定 Yoneda の形状同型を経由して大域比較の成分へ結ぶ。
Kerodon Definition 7.3.1.2（Tag 02Y9）。HTT 5.1.5.6 の指定大域比較。 -/
lemma weightedSections_nativeLimitIso_hom_transportGlobal
    {C : Type u} [SmallCategory C] {E : SSet.{u + 1}} [Quasicategory E]
    (O : Presheaf C E) (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (P : (PresheafCat C SpaceInfinity.{u}).op _⦋0⦌) :
    let a := fixedYonedaDomainIso C
    let b := (SSet.opFunctor.mapIso (fixedPresheafShapeIso C)).symm
    let O' := a.inv ≫ O
    let δ := SSet.opFunctor.map (yonedaInfinityMap (nerve C))
    let δ₀ := nativeSetShapeOppositeYoneda C
    let hw := nativeSetShapeOppositeYoneda_square C
    ∀ {G : (PresheafInfinity (nerve C)).op ⟶ E}
      (α : SSet.Homotopy (δ ≫ G) O')
      (hα : IsRightKanExtension δ O' G α)
      (h : a.hom ≫ O' = O)
      (t : RightKanConeTransport δ O' G α (b.hom.app (Opposite.op ⦋0⦌) P))
      (ht : IsLimitCone t.cone),
    let β := rightKanCounitIsoSquare a b hw α
    let hβ := kanRightKanExtension_of_isoSquare a b hw α hα
    let β' : SSet.Homotopy (δ₀ ≫ (b.hom ≫ G)) O := h ▸ β
    let hβ' : IsRightKanExtension δ₀ O (b.hom ≫ G) β' := by
      exact (show ∀ (O₀ O₁ : Presheaf C E) (hs : O₀ = O₁)
        (g : SSet.Homotopy (δ₀ ≫ (b.hom ≫ G)) O₀),
        IsRightKanExtension δ₀ O₀ (b.hom ≫ G) g →
        IsRightKanExtension δ₀ O₁ (b.hom ≫ G) (hs ▸ g) from
        fun _ _ hs _ hg => by cases hs; exact hg) _ _ h β hβ
    (weightedSections_nativeLimitIso O hE P t.cone ht).hom =
      functorHomEvaluate (weightedSections_nativeShape_comparison O hE β' hβ').hom P ≫
        eqToHom (congrArg HomotopyCategory.mk t.cone_vertex).symm := by
  intro a b O' δ δ₀ hw G α hα h t ht β hβ β' hβ'
  let s := rightKanTransportIsoSquare a b hw α P t
  let i := rightKanShapeIsoOfSquare a b hw P
  have hs' := (isLimitCone_iff_restrict_equivalentShape
    i.hom (isPrecompositionEquivalence_of_iso i).isQCatEquivalence t.cone).mp ht
  have hval := rightKanTransportIsoSquare_cone_val a b hw α P t
  have hs : IsLimitCone s.cone := (isLimitCone_iff_of_cone_val_eq _ _ hval).mpr hs'
  have hv : s.cone.vertex = t.cone.vertex := s.cone_vertex.trans t.cone_vertex.symm
  rw [weightedSections_nativeLimitIso_hom_through O hE P h s.cone t.cone hs ht,
    nativeLimitIsoOfCoefficientEq_hom_global O (a.hom ≫ O') hE h β hβ P s hs,
    rightKanLimitVertexIsoOfIsoSquare_hom_of_restriction a b hw O' P s.cone t.cone hs ht hval hv,
    Category.assoc, eqToHom_trans]

end SerrePositivity.InfinityCategories.Sheaves
