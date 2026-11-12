module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagZero

/-!
概要：相対旗を同じ全多次数の S 構造射で結び旗方向の前合成と照合する。
方針：wide 制限射を旗全体の持ち上げへ後合成する。
規約：多次数方向と旗方向の交換は元の ambient 関手圏で厳密に検査する。
使われ方：相対 S• の全方向を保持した実現前の図式。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：同じ指定射の相対旗を全多次数の S 構造射で写す。
方針：wide 部分複体間の実射を旗の持ち上げへ後合成する。
規約：旗の各辺を独立に選び直さない。
使われ方：相対旗の多次数方向の面・退化。 -/
def suppliedMultiRelativeFlagsMap (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    suppliedMultiRelativeFlags supply r ι f hf K ⟶
      suppliedMultiRelativeFlags supply r κ f hf K :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _
    (multiRelativeFlagsInclusion r ι Y (multiWideStageData supply r ι f hf).subcomplex K ≫
      (ihom K).map (((multiSEndofunctor r).map α).app Y).val) (by
        intro v
        obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v
        refine ⟨g ≫ multiWideStageMap supply r α f hf, ?_⟩
        exact congrArg (fun q =>
          ((ihom K).map (((multiSEndofunctor r).map α).app Y).val).app
            (Opposite.op ⦋0⦌) q) hg)

/-- 概要：全多次数方向の相対旗射は包含後に元の S 構造射の後合成となる。
方針：全部分複体への持ち上げの包含を計算する。
規約：同じ指定射を保持し、実現後だけの可換性へ弱めない。
使われ方：元の未置換 S 図式との比較の自然性。 -/
lemma suppliedMultiRelativeFlagsMap_inclusion (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    suppliedMultiRelativeFlagsMap supply r α f hf K ≫
      multiRelativeFlagsInclusion r κ Y (multiWideStageData supply r κ f hf).subcomplex K =
    multiRelativeFlagsInclusion r ι Y (multiWideStageData supply r ι f hf).subcomplex K ≫
      (ihom K).map (((multiSEndofunctor r).map α).app Y).val := rfl

/-- 概要：供給値の相対旗の前合成を同じ公開対象間の射として包む。
方針：各多次数で既存の旗前合成をそのまま使う。
規約：射の値を変えず、型検査で大きな供給証明を展開しない。
使われ方：全方向の交換則と単体的な相対旗の組立。 -/
def suppliedMultiRelativeFlagsPrecomp (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {L K : SSet.{u}} (i : L ⟶ K) :
    suppliedMultiRelativeFlags supply r ι f hf K ⟶
      suppliedMultiRelativeFlags supply r ι f hf L :=
  multiRelativeFlagsPrecomp r ι Y (multiWideStageData supply r ι f hf).subcomplex i

/-- 概要：相対旗の多次数方向と旗方向の作用は厳密に交換する。
方針：ambient 関手圏の前後合成の交換を部分型の値へ移す。
規約：全ての高次単体での等号を証明する。
使われ方：相対旗を多単体図式へ束ねる交換則。 -/
lemma suppliedMultiRelativeFlagsMap_precomp (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) {L K : SSet.{u}} (i : L ⟶ K) :
    suppliedMultiRelativeFlagsMap supply r α f hf K ≫
      suppliedMultiRelativeFlagsPrecomp supply r κ f hf i =
    suppliedMultiRelativeFlagsPrecomp supply r ι f hf i ≫
      suppliedMultiRelativeFlagsMap supply r α f hf L := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  apply Subtype.ext
  rfl

/-- 概要：相対旗を全 S 多次数と旗方向の全てで関手的に束ねる。
方針：厳密に交換する前後合成と元の反復 S の関手則を使う。
規約：対角へ制限せず、一般供給の自然な選択も要求しない。
使われ方：相対実現比較の全多単体的な入力。 -/
def suppliedMultiRelativeFlagDiagram (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (Fin r → SimplexCategoryᵒᵖ) ⥤ (SimplexCategoryᵒᵖ ⥤ SSet.{u}) where
  obj ι := multiRelativeFlagDiagram r ι Y (multiWideStageData supply r ι f hf).subcomplex
  map α := {
    app n := suppliedMultiRelativeFlagsMap supply r α f hf (SSet.stdSimplex.obj n.unop)
    naturality _ _ _ := by
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro s
      apply Subtype.ext
      rfl }
  map_id ι := by
    apply NatTrans.ext
    funext n
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    have h := congrArg
      (fun t : ((multiSEndofunctor r).obj ι) ⟶ ((multiSEndofunctor r).obj ι) => (t.app Y).val)
      ((multiSEndofunctor r).map_id ι)
    have hh := (congrArg (fun g => (ihom (SSet.stdSimplex.obj n.unop)).map g) h).trans
      ((ihom (SSet.stdSimplex.obj n.unop)).map_id _)
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hh d) s.val
  map_comp {ι κ μ} α β := by
    apply NatTrans.ext
    funext n
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    have h := congrArg
      (fun t : ((multiSEndofunctor r).obj ι) ⟶ ((multiSEndofunctor r).obj μ) => (t.app Y).val)
      ((multiSEndofunctor r).map_comp α β)
    have hh := (congrArg (fun g => (ihom (SSet.stdSimplex.obj n.unop)).map g) h).trans
      ((ihom (SSet.stdSimplex.obj n.unop)).map_comp _ _)
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hh d) s.val

/-- 概要：相対旗の零段比較は元の全 S 多次数の構造射と厳密に可換。
方針：包含と一点評価における後合成の計算。
規約：多次数ごとの独立な同型だけに弱めない。
使われ方：元の未置換 S 図式への自然な零段比較。 -/
lemma suppliedMultiRelativeFlagsMap_zero (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    suppliedMultiRelativeFlagsMap supply r α f hf Δ[0] ≫
      (multiRelativeFlagZeroIso supply r κ f hf).hom =
    (multiRelativeFlagZeroIso supply r ι f hf).hom ≫
      (((multiSEndofunctor r).map α).app Y).val := rfl

end SerrePositivity.KST.SConstruction.Cofinality
