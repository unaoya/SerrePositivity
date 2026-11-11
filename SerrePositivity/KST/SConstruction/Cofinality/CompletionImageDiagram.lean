module
public import SerrePositivity.KST.SConstruction.Cofinality.CompletionImageEquivalence
public import SerrePositivity.KST.SConstruction.ClosedSubcategoryFunctor

/-!
概要：元の指定射の閉じた本質像を全 S 多次数の厳密な図式に束ねる。
方針：元の全構造射を本質像へ制限し、包含後に関手則を検査する。
規約：本質像への同値の逆の選択に自然性を仮定しない。
使われ方：K-B2-S1 の左項を全多単体図式で元の始域と照合する。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：全 S 多次数の構造射は元の本質像を保つ。
方針：元の頂点同型を構造射で写し、元の f の厳密な自然性を使う。
規約：各多次数の本質像を独立な完備化模型へ置き換えない。
使われ方：構造射の閉じた本質像への制限。 -/
lemma completionImage_map_mem (r : ℕ) {ι κ : Fin r → SimplexCategoryᵒᵖ}
    (α : ι ⟶ κ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (y : (((multiSEndofunctor r).obj ι).obj Y).carrier _⦋0⦌)
    (hy : (completionImageClosedPredicate r ι f hf).predicate y) :
    (completionImageClosedPredicate r κ f hf).predicate
      ((((multiSEndofunctor r).map α).app Y).val.app (Opposite.op ⦋0⦌) y) := by
  obtain ⟨x, ⟨e⟩⟩ := hy
  refine ⟨(((multiSEndofunctor r).map α).app X).val.app (Opposite.op ⦋0⦌) x, ?_⟩
  have he := congrArg (fun q : ((multiSEndofunctor r).obj ι).obj X ⟶
      ((multiSEndofunctor r).obj κ).obj Y => q.val.app (Opposite.op ⦋0⦌) x)
    (((multiSEndofunctor r).map α).naturality f)
  exact he ▸ Nonempty.intro (e.map (((multiSEndofunctor r).map α).app Y).val)

/-- 概要：全 S 構造射を同じ閉じた本質像の間の完全関手へ制限する。
方針：像条件の保存を既存の全部分圏制限へ渡す。
規約：元の構造射を包含後に保持する。
使われ方：本質像の全多単体図式の射。 -/
def completionImageStructureMap (r : ℕ) {ι κ : Fin r → SimplexCategoryᵒᵖ}
    (α : ι ⟶ κ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    closedStableModel (completionImageClosedPredicate r ι f hf) ⟶
      closedStableModel (completionImageClosedPredicate r κ f hf) :=
  closedStableMap (completionImageClosedPredicate r ι f hf)
    (completionImageClosedPredicate r κ f hf) (((multiSEndofunctor r).map α).app Y)
      (completionImage_map_mem r α f hf)

/-- 概要：本質像の構造射は包含後に元の S 構造射を回収する。
方針：閉じた全部分圏の制限の包含公式を使う。
規約：安定模型の射の厳密な等号。
使われ方：相対供給と元の全多単体図式の照合。 -/
lemma completionImageStructureMap_inclusion (r : ℕ)
    {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionImageStructureMap r α f hf ≫
      closedStableInclusion (completionImageClosedPredicate r κ f hf) =
      closedStableInclusion (completionImageClosedPredicate r ι f hf) ≫
        ((multiSEndofunctor r).map α).app Y :=
  closedStableMap_inclusion _ _ _ _

/-- 概要：元の始域から本質像への実制限射は全多次数で厳密に自然。
方針：標的の包含を消去し、元の f の自然性へ戻す。
規約：独立に選んだ逆同値の自然性は使わない。
使われ方：本質像の左項から元の始域へ戻す全多単体的な比較。 -/
lemma completionSourceImageStableMap_naturality (r : ℕ)
    {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    ((multiSEndofunctor r).map α).app X ≫ completionSourceImageStableMap r κ f hf =
      completionSourceImageStableMap r ι f hf ≫ completionImageStructureMap r α f hf := by
  apply closedStableInclusion_cancel (completionImageClosedPredicate r κ f hf)
  exact ((Category.assoc _ _ _).trans
    (congrArg (fun q => ((multiSEndofunctor r).map α).app X ≫ q)
      (completionSourceImageStableMap_inclusion r κ f hf))).trans
    ((((multiSEndofunctor r).map α).naturality f).symm.trans
      (((congrArg (fun q => q ≫ ((multiSEndofunctor r).map α).app Y)
        (completionSourceImageStableMap_inclusion r ι f hf)).symm.trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun q => completionSourceImageStableMap r ι f hf ≫ q)
              (completionImageStructureMap_inclusion r α f hf).symm))).symm))

/-- 概要：閉じた本質像の安定模型は全 S 多次数の厳密な図式をなす。
方針：元の構造射の恒等・合成則を包含の消去で反映する。
規約：実現前の StableModel 値図式として束ねる。
使われ方：相対 fiber 供給へ渡す全多単体的な左項。 -/
def completionImageDiagram (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ StableModel.{u} where
  obj ι := closedStableModel (completionImageClosedPredicate r ι f hf)
  map α := completionImageStructureMap r α f hf
  map_id ι := by
    apply closedStableInclusion_cancel (completionImageClosedPredicate r ι f hf)
    exact (completionImageStructureMap_inclusion r (𝟙 ι) f hf).trans
      ((congrArg (fun q : ((multiSEndofunctor r).obj ι) ⟶
          ((multiSEndofunctor r).obj ι) =>
          closedStableInclusion (completionImageClosedPredicate r ι f hf) ≫ q.app Y)
        ((multiSEndofunctor r).map_id ι)).trans
          ((Category.comp_id _).trans (Category.id_comp _).symm))
  map_comp {ι κ μ} α β := by
    apply closedStableInclusion_cancel (completionImageClosedPredicate r μ f hf)
    have h := congrArg (fun q : ((multiSEndofunctor r).obj ι) ⟶
        ((multiSEndofunctor r).obj μ) =>
        closedStableInclusion (completionImageClosedPredicate r ι f hf) ≫ q.app Y)
      ((multiSEndofunctor r).map_comp α β)
    calc
      completionImageStructureMap r (α ≫ β) f hf ≫
          closedStableInclusion (completionImageClosedPredicate r μ f hf) =
          closedStableInclusion (completionImageClosedPredicate r ι f hf) ≫
            ((multiSEndofunctor r).map (α ≫ β)).app Y :=
        completionImageStructureMap_inclusion r (α ≫ β) f hf
      _ = closedStableInclusion (completionImageClosedPredicate r ι f hf) ≫
          (((multiSEndofunctor r).map α).app Y ≫
            ((multiSEndofunctor r).map β).app Y) := h
      _ = (closedStableInclusion (completionImageClosedPredicate r ι f hf) ≫
          ((multiSEndofunctor r).map α).app Y) ≫
            ((multiSEndofunctor r).map β).app Y := (Category.assoc _ _ _).symm
      _ = (completionImageStructureMap r α f hf ≫
          closedStableInclusion (completionImageClosedPredicate r κ f hf)) ≫
            ((multiSEndofunctor r).map β).app Y := congrArg
        (fun q => q ≫ ((multiSEndofunctor r).map β).app Y)
          (completionImageStructureMap_inclusion r α f hf).symm
      _ = completionImageStructureMap r α f hf ≫
          (completionImageStructureMap r β f hf ≫
            closedStableInclusion (completionImageClosedPredicate r μ f hf)) :=
        (Category.assoc _ _ _).trans (congrArg
          (fun q => completionImageStructureMap r α f hf ≫ q)
            (completionImageStructureMap_inclusion r β f hf).symm)
      _ = _ := (Category.assoc _ _ _).symm

/-- 概要：元の始域から本質像への制限は全多単体図式の自然変換。
方針：実装した厳密な前合成可換性を束ねる。
規約：各成分は元の指定反復 S 射の本質像への制限。
使われ方：供給の左項を全多次数で元の始域へ戻す。 -/
def completionSourceImageNatTrans (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    multiSEndofunctor r ⋙ (evaluation StableModel StableModel).obj X ⟶
      completionImageDiagram r f hf where
  app ι := completionSourceImageStableMap r ι f hf
  naturality {_ι _κ} α := completionSourceImageStableMap_naturality r α f hf

end SerrePositivity.KST.SConstruction.Cofinality
