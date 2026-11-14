module
public import SerrePositivity.KST.SConstruction.Cofinality.ImageComponentObstruction
public import SerrePositivity.KST.SConstruction.Cofinality.WideInvertibleReflection

/-!
概要：元の始域像は同じ wide 模型の一つの基点成分を正確に与える。
方針：始域の零射と ambient 可逆辺を wide の辺として持ち上げる。
規約：離散的障害の群構造や K₀ の商との同定は別に残す。
使われ方：相対旗の回収条件を基点成分への所属として記述する。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の始域から具体的な全辺 wide 模型への指定射。
方針：供給値への既存因子化を模型の等号で移す。
規約：包含後は元の同じ反復 S 射。
使われ方：wide 成分の基点を元の始域から指定する。 -/
def completionCanonicalSourceToWide (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (((multiSEndofunctor r).obj ι).obj X).carrier ⟶
      (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) :=
  multiSourceToWide stableWideCofinalitySupply r ι f hf ≫
    Subcomplex.homOfLE (completionMultiWide_eq r ι f hf).le

/-- 概要：周囲で同型な wide 頂点は同じ wide 成分にある。
方針：周囲の同型を表す可逆辺を分母辺として持ち上げる。
規約：周囲の全辺ではなく可逆辺だけに適用する。
使われ方：本質像の同型を成分の等号へ移す。 -/
lemma completionWideComponent_eq_of_vertexIso (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (x y : (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) _⦋0⦌)
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x.val y.val) : SSet.π₀.mk x = SSet.π₀.mk y := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  obtain ⟨a, ha⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective x.val y.val e.hom
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a := by
    change IsIso (Truncated.HomotopyCategory.homMk a)
    rw [ha]
    infer_instance
  let b : (LocalizingInvariants.completionCofiberWide F.val : SSet.{u}) _⦋1⦌ :=
    ⟨a.edge, LocalizingInvariants.completionCofiberWide_edge F.val
      (multiSEndofunctor_map_isIdempotentCompletion r ι f hf) a.edge
        (completionMulti_invertibleEdge_mem r ι f hf a.edge
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := a) (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a.edge) rfl).mp hi))⟩
  exact SSet.π₀.sound (SSet.Edge.mk b (Subtype.ext a.src_eq) (Subtype.ext a.tgt_eq))

/-- 概要：元の始域の全頂点の像は一つの wide 成分にある。
方針：始域のホモトピー圏の零射を辺で表し、同じ指定因子化で写す。
規約：始域の完備性や K₀ 全射性を使わない。
使われ方：像成分の基点の選択非依存性。 -/
lemma completionSourceWide_component_eq (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (x y : (((multiSEndofunctor r).obj ι).obj X).carrier _⦋0⦌) :
    SSet.π₀.mk ((completionCanonicalSourceToWide r ι f hf).app (Opposite.op ⦋0⦌) x) =
      SSet.π₀.mk ((completionCanonicalSourceToWide r ι f hf).app (Opposite.op ⦋0⦌) y) := by
  let z := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.chosenZeroVertex (((multiSEndofunctor r).obj ι).obj X).carrier
  obtain ⟨a, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective z.vertex x
    (z.isInitial.isInitialHo.to (HomotopyCategory.mk x))
  obtain ⟨b, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.homotopyCategory_homMk_surjective z.vertex y
    (z.isInitial.isInitialHo.to (HomotopyCategory.mk y))
  exact (SSet.π₀.sound ((SSet.Edge.ofTruncated a).map
    (completionCanonicalSourceToWide r ι f hf))).symm.trans
      (SSet.π₀.sound ((SSet.Edge.ofTruncated b).map
        (completionCanonicalSourceToWide r ι f hf)))

/-- 概要：wide の像所属述語は元の始域の任意の頂点の像成分への所属に等しい。
方針：本質像の同型を wide 成分へ移し、始域内の零射で基点と結ぶ。
規約：元の指定射の本質像を正確に特徴づける。
使われ方：相対旗の回収を基点成分の障害として読む。 -/
theorem completionWideImageComponent_iff_basepoint (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (x : (((multiSEndofunctor r).obj ι).obj X).carrier _⦋0⦌)
    (y : (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) _⦋0⦌) :
    completionWideImageComponent r ι f hf (SSet.π₀.mk y) ↔
      SSet.π₀.mk y = SSet.π₀.mk
        ((completionCanonicalSourceToWide r ι f hf).app (Opposite.op ⦋0⦌) x) := by
  let G := completionCanonicalSourceToWide r ι f hf
  constructor
  · rintro ⟨a, ⟨e⟩⟩
    have he : SSet.π₀.mk (G.app (Opposite.op ⦋0⦌) a) = SSet.π₀.mk y :=
      completionWideComponent_eq_of_vertexIso r ι f hf _ y e
    exact he.symm.trans (completionSourceWide_component_eq r ι f hf a x)
  · intro hy
    exact (completionMultiWideComponent_image_iff r ι f hf y
      (G.app (Opposite.op ⦋0⦌) x) hy).mpr ⟨x, ⟨Iso.refl _⟩⟩

/-- 概要：連結な相対旗の回収障害は、任意の始域頂点の像との成分差である。
方針：成分上の像述語の判定と、像成分の基点による特徴づけを合成する。
規約：障害は同じ具体的 wide 模型の成分集合で測る。
使われ方：加法的 fiber 比較へ渡す基点成分の判定。 -/
theorem completionRelativeFlag_recovery_iff_basepoint (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {K : SSet.{u}} [K.IsPreconnected]
    (v : (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) _⦋0⦌)
    (g : K ⟶ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}))
    (hg : g ≫ (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val).ι =
      completionRelativeFlagVertexFunctor r ι f hf v) (k : K _⦋0⦌)
    (x : (((multiSEndofunctor r).obj ι).obj X).carrier _⦋0⦌) :
    (∃ s : ((ihom K).obj (((multiSEndofunctor r).obj ι).obj X).carrier) _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((multiSourceToRelativeFlags stableWideCofinalitySupply r ι f hf K).app
        (Opposite.op ⦋0⦌) s) v)) ↔
      SSet.π₀.mk (g.app (Opposite.op ⦋0⦌) k) = SSet.π₀.mk
        ((completionCanonicalSourceToWide r ι f hf).app (Opposite.op ⦋0⦌) x) :=
  (completionRelativeFlag_recovery_iff_imageComponent r ι f hf v g hg k).trans
    (completionWideImageComponent_iff_basepoint r ι f hf x _)

end SerrePositivity.KST.SConstruction.Cofinality
