module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagDiagram
public import SerrePositivity.KST.SConstruction.FunctorVertexEvaluation

/-!
概要：相対旗の零段を元の未置換 S 対象へ戻す。
方針：恒等辺の零 cofiber から wide 部分複体の全頂点性を確認する。
規約：亜群化や Kan 置換の後の零段で代用しない。
使われ方：元の K 射を含む相対 S• 図式の零段の照合。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：供給された wide 部分複体は元の標的の全頂点を含む。
方針：恒等辺の cofiber が零であり元の完全射の像に入ることを使う。
規約：全頂点性を追加の供給仮定としない。
使われ方：相対旗の未置換零段の比較。 -/
lemma WideStageData.vertex_mem {X Y : StableModel.{u}} (f : X ⟶ Y)
    (d : WideStageData f) (y : Y.carrier _⦋0⦌) :
    y ∈ d.subcomplex.obj (Opposite.op ⦋0⦌) := by
  apply (d.simplex_spec 0 y).mpr
  intro θ
  have hθ : θ = SimplexCategory.σ 0 := by
    ext i
    have hz : (⦋0⦌ : SimplexCategory).len = 0 := rfl
    omega
  have hy : Y.carrier.map θ.op y = (SSet.Truncated.Edge.id
      (X := (truncation 2).obj Y.carrier) y).edge :=
    congrArg (fun q => Y.carrier.map q.op y) hθ
  let a := SSet.Truncated.Edge.id (X := (truncation 2).obj Y.carrier) y
  let s := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare a
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a := by
    change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
    have h := SSet.Truncated.HomotopyCategory.homMk_id
      (V := (truncation 2).obj Y.carrier) y
    exact h.symm ▸ (inferInstance : IsIso (𝟙 (HomotopyCategory.mk y : hoFunctor.obj Y.carrier)))
  let t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a.edge) := {
    toZeroTriangle := s.toZeroTriangle
    bottom_edge := s.bottom_edge
    isPushout := s.isPushout }
  let x := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X.carrier
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor f.val := stableModelHom_exact f
  have hz := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero (F := f.val) x.vertex x.isZero
  have e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso t.cofiber (f.val.app (Opposite.op ⦋0⦌) x.vertex) :=
    (s.zero_of_homMk_isIso hi).isZeroHo.iso hz.isZeroHo
  have hm : a.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {z | ∃ v, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (f.val.app (Opposite.op ⦋0⦌) v) z)} :=
    ⟨t, f.val.app (Opposite.op ⦋0⦌) x.vertex, ⟨x.vertex, ⟨Iso.refl _⟩⟩, ⟨e⟩⟩
  exact hy ▸ hm

/-- 概要：供給値から定まる一点の相対旗条件は全ての元の旗に成立する。
方針：Yoneda 表示で一点の旗を頂点へ戻し、wide の全頂点性で持ち上げる。
規約：零段の旗は元の未置換反復 S 内のものを使う。
使われ方：相対旗の零段の包含の同型性。 -/
lemma multiRelativeFlagPredicate_point (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (v : ((ihom (Δ[0] : SSet.{u})).obj
      (((multiSEndofunctor r).obj ι).obj Y).carrier) _⦋0⦌) :
    multiRelativeFlagPredicate r ι Y (multiWideStageData supply r ι f hf).subcomplex Δ[0] v := by
  obtain ⟨F, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv Δ[0] _).surjective v
  let d := multiWideStageData supply r ι f hf
  let y : (d.subcomplex : SSet.{u}) _⦋0⦌ :=
    ⟨SSet.yonedaEquiv F, d.vertex_mem _ _⟩
  let g : (Δ[0] : SSet.{u}) ⟶ (d.subcomplex : SSet.{u}) := SSet.yonedaEquiv.symm y
  have he : g ≫ d.subcomplex.ι = F := by
    apply SSet.yonedaEquiv.injective
    exact congrArg Subtype.val (SSet.yonedaEquiv.apply_symm_apply y)
  exact ⟨g, congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex he⟩

/-- 概要：相対旗の未置換零段の包含は元の一点関手圏との同型。
方針：全頂点で成立する相対条件を付ける射を逆射とする。
規約：亜群化や Kan 置換を使わない厳密な単体集合の同型。
使われ方：元の S 図式の零段への接続。 -/
def multiRelativeFlagPointInclusionIso (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    suppliedMultiRelativeFlags supply r ι f hf Δ[0] ≅
      (ihom (Δ[0] : SSet.{u})).obj (((multiSEndofunctor r).obj ι).obj Y).carrier where
  hom := multiRelativeFlagsInclusion r ι Y (multiWideStageData supply r ι f hf).subcomplex Δ[0]
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (𝟙 _)
    (multiRelativeFlagPredicate_point supply r ι f hf)
  hom_inv_id := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    rfl
  inv_hom_id := rfl

/-- 概要：相対旗の未置換零段は元の同じ全多次数の S 対象に同型。
方針：相対旗の包含同型と既存の一点評価同型を合成する。
規約：元の反復 S を別の完備化模型へ置き換えない。
使われ方：同じ元の K 射へ戻る零段比較。 -/
def multiRelativeFlagZeroIso (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    suppliedMultiRelativeFlags supply r ι f hf Δ[0] ≅
      (((multiSEndofunctor r).obj ι).obj Y).carrier :=
  multiRelativeFlagPointInclusionIso supply r ι f hf ≪≫ pointFunctorEvaluationIso _

end SerrePositivity.KST.SConstruction.Cofinality
