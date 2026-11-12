module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagSourceRecovery

/-!
概要：実際の相対旗の頂点を、像成分の条件から元の始域の旗へ回収する。
方針：旗全体の wide 持ち上げを取り出し、連結な族の回収を全部分圏内へ反映する。
規約：単なる周囲の関手同型ではなく、同じ相対旗圏内の頂点同型を得る。
使われ方：相対 S• の像成分の始域側との比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：相対旗の頂点を元の同じ多次数の関手として読む。
方針：ambient 内部 Hom の頂点表示の逆を使う。
規約：旗の全高次図式を保持する。
使われ方：指定頂点の像所属条件の評価。 -/
def completionRelativeFlagVertexFunctor (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) {K : SSet.{u}}
    (v : (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) _⦋0⦌) :
    K ⟶ (((multiSEndofunctor r).obj ι).obj Y).carrier :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K _).symm v.val

/-- 概要：実際の相対旗は元の具体的な wide 模型へ全体として持ち上がる。
方針：定義の所属証明から全旗の持ち上げを取り出し、全辺模型の等号で移す。
規約：旗の各辺を独立に選ばない。
使われ方：像成分の全図式回収への実入力。 -/
theorem exists_completionRelativeFlagVertexLift (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) {K : SSet.{u}}
    (v : (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) _⦋0⦌) :
    ∃ g : K ⟶ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}),
      g ≫ (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val).ι =
        completionRelativeFlagVertexFunctor r ι f hf v := by
  obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
  let hM := (completionMultiWide_eq r ι f hf).le
  refine ⟨g ≫ Subcomplex.homOfLE hM, ?_⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  have he := (Category.assoc g (Subcomplex.homOfLE hM) _).trans
    (congrArg (fun t => g ≫ t) (Subcomplex.homOfLE_ι hM))
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (completionRelativeFlagVertexFunctor r ι f hf v) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K _).apply_symm_apply v.val
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex he).trans (hg.trans hv.symm)

/-- 概要：連結な相対旗の一頂点の像所属から、旗自身を元の始域の旗として回収する。
方針：全体の wide 持ち上げを像成分の全族回収へ渡し、全包含の充満忠実性で戻す。
規約：同型は ambient だけでなく相対旗圏内にある。
使われ方：相対 S• の像成分の本質全射性。 -/
theorem exists_completionSourceFlagVertexIso (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {K : SSet.{u}} [K.IsPreconnected]
    (v : (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) _⦋0⦌)
    (k₀ : K _⦋0⦌)
    (hk₀ : (completionRelativeFlagVertexFunctor r ι f hf v).app (Opposite.op ⦋0⦌) k₀ ∈
      LocalizingInvariants.completionEssentialImage (((multiSEndofunctor r).obj ι).map f).val) :
    ∃ s : ((ihom K).obj (((multiSEndofunctor r).obj ι).obj X).carrier) _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
        ((multiSourceToRelativeFlags stableWideCofinalitySupply r ι f hf K).app
          (Opposite.op ⦋0⦌) s) v) := by
  obtain ⟨g, hg⟩ := exists_completionRelativeFlagVertexLift r ι f hf v
  have hpoint := congrArg (fun q : K ⟶ (((multiSEndofunctor r).obj ι).obj Y).carrier =>
    q.app (Opposite.op ⦋0⦌) k₀) hg
  have hk' : (g.app (Opposite.op ⦋0⦌) k₀).val ∈
      LocalizingInvariants.completionEssentialImage (((multiSEndofunctor r).obj ι).map f).val :=
    Eq.mpr (congrArg (fun y => y ∈ LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val) hpoint) hk₀
  obtain ⟨G, ⟨e⟩⟩ := exists_multiSourceFamily_of_relative_component r ι f hf g k₀ hk'
  let e' := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e rfl hg
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G, ⟨?_⟩⟩
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).preimageVertexIso
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (G ≫ (((multiSEndofunctor r).obj ι).map f).val)) v.val
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (completionRelativeFlagVertexFunctor r ι f hf v) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K _).apply_symm_apply v.val
  exact hv ▸ e'

/-- 概要：始域の旗と同型な相対旗の各頂点は元の本質像に属する。
方針：相対旗内の同型を包含と指定頂点評価で写す。
規約：周囲の関手同型を頂点の等号と混同しない。
使われ方：像成分の相対旗の逆向きの判定。 -/
lemma completionSourceFlagVertexIso_image (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) {K : SSet.{u}}
    (s : ((ihom K).obj (((multiSEndofunctor r).obj ι).obj X).carrier) _⦋0⦌)
    (v : (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((multiSourceToRelativeFlags stableWideCofinalitySupply r ι f hf K).app
      (Opposite.op ⦋0⦌) s) v) (k : K _⦋0⦌) :
    (completionRelativeFlagVertexFunctor r ι f hf v).app (Opposite.op ⦋0⦌) k ∈
      LocalizingInvariants.completionEssentialImage (((multiSEndofunctor r).obj ι).map f).val := by
  obtain ⟨G, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K _).surjective s
  let E := multiRelativeFlagsInclusion r ι Y
    (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex K ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (((multiSEndofunctor r).obj ι).obj Y).carrier) k
  have eD := e.map E
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (G ≫ (((multiSEndofunctor r).obj ι).map f).val)))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app (Opposite.op ⦋0⦌) v.val) at eD
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (completionRelativeFlagVertexFunctor r ι f hf v) = v.val :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K _).apply_symm_apply v.val
  have htarget := (congrArg (fun w =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (((multiSEndofunctor r).obj ι).obj Y).carrier) k).app
      (Opposite.op ⦋0⦌) w) hv).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex k (completionRelativeFlagVertexFunctor r ι f hf v))
  have hsource := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex k
    (G ≫ (((multiSEndofunctor r).obj ι).map f).val)
  refine ⟨G.app (Opposite.op ⦋0⦌) k, ⟨?_⟩⟩
  exact hsource ▸ htarget ▸ eD

/-- 概要：連結なパラメータの相対旗は指定一頂点の像所属だけで始域像を判定できる。
方針：全図式の回収と、相対旗内の同型の頂点評価を組み合わせる。
規約：始域像は同じ元の反復 S 射の本質像である。
使われ方：相対 S• の像成分の全部分圏の同定。 -/
theorem completionSourceFlagVertexImage_iff (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {K : SSet.{u}} [K.IsPreconnected]
    (v : (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) _⦋0⦌)
    (k₀ : K _⦋0⦌) :
    (∃ s : ((ihom K).obj (((multiSEndofunctor r).obj ι).obj X).carrier) _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((multiSourceToRelativeFlags stableWideCofinalitySupply r ι f hf K).app
        (Opposite.op ⦋0⦌) s) v)) ↔
      (completionRelativeFlagVertexFunctor r ι f hf v).app (Opposite.op ⦋0⦌) k₀ ∈
        LocalizingInvariants.completionEssentialImage
          (((multiSEndofunctor r).obj ι).map f).val := by
  constructor
  · rintro ⟨s, ⟨e⟩⟩
    exact completionSourceFlagVertexIso_image r ι f hf s v e k₀
  · exact exists_completionSourceFlagVertexIso r ι f hf v k₀

end SerrePositivity.KST.SConstruction.Cofinality
