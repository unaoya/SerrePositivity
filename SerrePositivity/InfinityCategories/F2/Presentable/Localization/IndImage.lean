module

public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.IndCandidate
public import SerrePositivity.InfinityCategories.F2.Presentable.Localization.GeneratedArrowColimits
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FullyFaithfulPostcomposition
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanDiagramColimitTransport

/-!
概要：実 Ind 比較の同型で飽和した像と、その κ-filtered 余極限閉性。
方針：F1 の実頂点像への同値を使って図式全体を Ind へ持ち上げ、同じ余錐で比較する。
規約：比較の充満忠実性は明示した条件。未供給の証明や全小余極限閉性は主張しない。
使われ方：P-1 f2、Ind 像の強飽和性に向けた filtered 閉性の工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.Localization
open HomotopyLimits
variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C] {I : Type u} (edges : I → C _⦋1⦌)
  (G : Ind.IndInfinity κ A ⟶ generatedArrowCategory edges)

/-- 元の射圏内で、実 Ind 比較の像の一つと同型を持つこと。 -/
def IndArrowImageVertex (f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌) : Prop :=
  ∃ a : (Ind.IndInfinity κ A) _⦋0⦌,
    Nonempty (VertexIso ((G ≫ generatedArrowInclusion edges).app _ a) f)

/-- 実 Ind 比較の像を同型で飽和した、元の射圏の全部分圏。 -/
def indArrowImageCategory : SSet.{u + 1} :=
  fullSubcomplexOnVertices _ (IndArrowImageVertex edges G)

instance indArrowImageCategory_quasicategory : Quasicategory (indArrowImageCategory edges G) :=
  fullSubcomplexOnVertices_quasicategory _ _

/-- 像から元の射圏への包含。 -/
def indArrowImageInclusion : indArrowImageCategory edges G ⟶
    (ihom (Δ[1] : SSet.{u + 1})).obj C :=
  (fullSubcomplexOnVertices _ (IndArrowImageVertex edges G)).ι

/-- 同じ実 Ind 比較の、像への因子化。 -/
def indArrowImageFactor : Ind.IndInfinity κ A ⟶ indArrowImageCategory edges G :=
  fullSubcomplexLift (IndArrowImageVertex edges G) (G ≫ generatedArrowInclusion edges)
    (fun a ↦ ⟨a, ⟨Iso.refl _⟩⟩)

omit [Fact κ.IsRegular] in
/-- 因子化の順射は元の実 Ind 比較を厳密に回収する。 -/
lemma indArrowImageFactor_inclusion :
    indArrowImageFactor edges G ≫ indArrowImageInclusion edges G =
      G ≫ generatedArrowInclusion edges := rfl

omit [Fact κ.IsRegular] in
/-- Ind 像の頂点条件は、元の射圏内の同型で不変。 -/
lemma indArrowImageVertex_iff_vertexIso {f g : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌}
    (e : VertexIso f g) : IndArrowImageVertex edges G f ↔ IndArrowImageVertex edges G g := by
  constructor
  · rintro ⟨a, ⟨ha⟩⟩
    exact ⟨a, ⟨ha ≪≫ e⟩⟩
  · rintro ⟨a, ⟨ha⟩⟩
    exact ⟨a, ⟨ha ≪≫ e.symm⟩⟩

omit [Fact κ.IsRegular] in
/-- 実 Ind 比較の像は、元の強飽和生成閉包の中にある。 -/
lemma indArrowImageVertex_mem {f : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌}
    (hf : IndArrowImageVertex edges G f) : arrowVertexEdge f ∈ generatedEdges edges := by
  obtain ⟨a, ⟨ha⟩⟩ := hf
  exact (generatedArrow_mem_iff_vertexIso edges ha).mp
    (fullSubcomplexOnVertices_vertex (G.app _ a))

omit [Fact κ.IsRegular] in
/-- 充満忠実な実比較は、その同型飽和した像への同値を与える。
F1 の頂点像の同値を再利用し、同型飽和への包含だけを接続する。 -/
lemma indArrowImageFactor_isQCatEquivalence (hG : IsFullyFaithful G) :
    IsQCatEquivalence (indArrowImageFactor edges G) := by
  let H := G ≫ generatedArrowInclusion edges
  let V : ((ihom (Δ[1] : SSet.{u + 1})).obj C) _⦋0⦌ → Prop :=
    fun f ↦ ∃ a, H.app _ a = f
  let q := fullSubcomplexLift V H (fun a ↦ ⟨a, rfl⟩)
  have hq : IsQCatEquivalence q := fullSubcomplexVertexImageLift_isQCatEquivalence H
    (hG.comp (generatedArrowInclusion_isFullyFaithful edges))
  let j : (fullSubcomplexOnVertices _ V : SSet.{u + 1}) ⟶ indArrowImageCategory edges G :=
    fullSubcomplexLift (IndArrowImageVertex edges G) (fullSubcomplexOnVertices _ V).ι (by
      intro f
      obtain ⟨a, ha⟩ := fullSubcomplexOnVertices_vertex f
      exact ⟨a, ⟨eqToIso (congrArg HomotopyCategory.mk ha)⟩⟩)
  have hj : IsQCatEquivalence j := by
    apply isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
    · apply (isFullyFaithful_fullSubcomplexOnVertices_ι _
        (IndArrowImageVertex edges G)).cancel_right
      change IsFullyFaithful (fullSubcomplexOnVertices _ V).ι
      exact isFullyFaithful_fullSubcomplexOnVertices_ι _ _
    · intro f
      obtain ⟨a, ⟨ha⟩⟩ := fullSubcomplexOnVertices_vertex f
      exact ⟨q.app _ a, ⟨(isFullyFaithful_fullSubcomplexOnVertices_ι _
        (IndArrowImageVertex edges G)).preimageVertexIso ha⟩⟩
  have he : q ≫ j = indArrowImageFactor edges G := by
    have : Mono (indArrowImageInclusion edges G) :=
      inferInstanceAs (Mono (fullSubcomplexOnVertices _ (IndArrowImageVertex edges G)).ι)
    apply (cancel_mono (indArrowImageInclusion edges G)).1
    change (q ≫ j) ≫ (fullSubcomplexOnVertices _ (IndArrowImageVertex edges G)).ι = _
    rw [Category.assoc, fullSubcomplexLift_ι, fullSubcomplexLift_ι,
      indArrowImageFactor_inclusion]
  have hh := hq.comp hj
  rwa [he] at hh

/-- 像は同じ κ に関して accessible。充満忠実性は公開後の実証拠を渡す。 -/
lemma indArrowImage_isKappaAccessible (hG : IsFullyFaithful G) :
    IsKappaAccessible κ (indArrowImageCategory edges G) :=
  (indInfinity_isKappaAccessible κ A).of_equivalence
    (indArrowImageFactor_isQCatEquivalence edges G hG).choose

omit [Fact κ.IsRegular] in
/-- Ind 像に値を持つ小さい κ-filtered 図式の、元の射圏の余極限も同じ像に属する。 -/
lemma indArrowImage_colimit_mem (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (hG : IsFullyFaithful G) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G)
    {K : SSet.{u}} [Quasicategory K] [IsKappaFiltered κ K]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ indArrowImageCategory edges G)
    (c : JoinCocone (D ≫ indArrowImageInclusion edges G)) (hc : IsColimitCone c) :
    IndArrowImageVertex edges G c.vertex := by
  let e := (indArrowImageFactor_isQCatEquivalence edges G hG).choose
  let H := G ≫ generatedArrowInclusion edges
  let L := D ≫ e.inv
  obtain ⟨d, hd⟩ := Ind.ind_hasSmallKappaFilteredColimits κ A K L
  have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ H := hp.comp
    ((generatedArrowInclusion_preservesSmallColimits hC edges).isKappaAccessibleFunctor κ)
  have hHd : IsColimitCone (mapJoinCocone H d) := hH K L d hd
  have he : FunctorIso (L ≫ H) (D ≫ indArrowImageInclusion edges G) := by
    rw [show H = e.hom ≫ indArrowImageInclusion edges G from
      (indArrowImageFactor_inclusion edges G).symm]
    simpa only [L, Category.assoc, Category.id_comp] using
      (e.invHomIso.precomp D).postcomp (indArrowImageInclusion edges G)
  obtain ⟨d', hd', hv⟩ := exists_colimitCocone_functorIso_sameVertex he (mapJoinCocone H d) hHd
  refine ⟨d.vertex, ⟨?_⟩⟩
  exact eqToIso (congrArg HomotopyCategory.mk (hv.trans (Ind.mapJoinCocone_vertex H d)).symm) ≪≫
    VertexIso.map (colimitConeIso d' c hd' hc)
      (sliceUnderProjection (D ≫ indArrowImageInclusion edges G))

omit [Fact κ.IsRegular] in
/-- 同型で飽和した実像の包含は充満忠実。 -/
lemma indArrowImageInclusion_isFullyFaithful :
    IsFullyFaithful (indArrowImageInclusion edges G) :=
  isFullyFaithful_fullSubcomplexOnVertices_ι _ _

omit [Fact κ.IsRegular] in
/-- 実像の指定された全 κ-filtered 余錐を、元の射圏の余極限として保存する。 -/
lemma indArrowImageInclusion_isKappaAccessible (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (hG : IsFullyFaithful G) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (indArrowImageInclusion edges G) := by
  intro K hK hκ D c hc
  obtain ⟨c₀, hc₀⟩ := functor_hasSmallColimits (Δ[1] : SSet.{u + 1}) hC K
    (D ≫ indArrowImageInclusion edges G)
  let P := IndArrowImageVertex edges G
  have hm := indArrowImage_colimit_mem edges G hC hG hp D c₀ hc₀
  let d := Ind.fullCoconeLift P D c₀ hm
  have hd : IsColimitCone d := Ind.fullCoconeLift_isColimit P D c₀ hm hc₀
  have hi : IsColimitCone (mapJoinCocone (indArrowImageInclusion edges G) d) := by
    change IsColimitCone (mapJoinCocone (fullSubcomplexOnVertices _ P).ι
      (Ind.fullCoconeLift P D c₀ hm))
    rw [Ind.fullCoconeLift_inclusion]
    exact hc₀
  exact Ind.mapJoinCocone_isColimit_of_functorIso (indArrowImageInclusion edges G)
    (Iso.refl _) d c hd hc hi

end SerrePositivity.InfinityCategories.F2.Presentable.Localization
