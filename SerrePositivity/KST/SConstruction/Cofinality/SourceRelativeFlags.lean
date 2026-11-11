module
public import SerrePositivity.KST.SConstruction.Cofinality.MultiRelativeFlags

/-!
概要：元の始域の反復 S 図式を同じ多次数の相対旗へ送る。
方針：始域の cofiber 四角形の完全な像から wide 所属を証明する。
規約：包含後に元の指定射の後合成を厳密に回収する。
使われ方：相対 S• 側から元の K 射へ戻る実射の照合。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の反復 S の始域からの全単体は指定 wide 部分複体に入る。
方針：各辺の実 cofiber を完全射で写し、その頂点が元の像に属することを使う。
規約：始域の完備性は仮定しない。
使われ方：元の指定射の wide 部分複体への因子化。 -/
lemma multiSource_mem_wide (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (n : ℕ) (s : (((multiSEndofunctor r).obj ι).obj X).carrier _⦋n⦌) :
    ((((multiSEndofunctor r).obj ι).map f).val.app (Opposite.op ⦋n⦌) s) ∈
      (multiWideStageData supply r ι f hf).subcomplex.obj (Opposite.op ⦋n⦌) := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  apply ((multiWideStageData supply r ι f hf).simplex_spec n _).mpr
  intro θ
  let a := (((multiSEndofunctor r).obj ι).obj X).carrier.map θ.op s
  let q := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.chosenCofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a)
  let t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.CofiberSquare (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (F.val.app (Opposite.op ⦋1⦌) a)) := {
    toZeroTriangle := (q.map F.val).toZeroTriangle
    bottom_edge := (q.map F.val).bottom_edge
    isPushout := (q.map F.val).isPushout }
  have hm : F.val.app (Opposite.op ⦋1⦌) a ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges
      {y | ∃ x, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (F.val.app (Opposite.op ⦋0⦌) x) y)} :=
    ⟨t, F.val.app (Opposite.op ⦋0⦌) q.cofiber,
      ⟨q.cofiber, ⟨Iso.refl _⟩⟩, ⟨Iso.refl _⟩⟩
  exact (ConcreteCategory.congr_hom (F.val.naturality θ.op) s) ▸ hm

/-- 概要：元の指定射を同じ全多次数の wide 部分複体へ因子化する。
方針：元の各単体の像に全辺条件の保存を添える。
規約：包含後の元の射を変更しない。
使われ方：始域の全旗を相対旗へ写す実射。 -/
def multiSourceToWide (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (((multiSEndofunctor r).obj ι).obj X).carrier ⟶
      ((multiWideStageData supply r ι f hf).subcomplex : SSet.{u}) where
  app d := ↾fun s => ⟨(((multiSEndofunctor r).obj ι).map f).val.app d s,
    multiSource_mem_wide supply r ι f hf d.unop.len s⟩
  naturality {d e} α := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((((multiSEndofunctor r).obj ι).map f).val.naturality α) s

/-- 概要：始域の全旗を同じ多次数の相対旗へ写す。
方針：元の旗を wide 因子化と合成して全体の持ち上げを示す。
規約：射は元の完全射による後合成を包含後に厳密に回収する。
使われ方：元の K 射を含む相対旗図式の始域射。 -/
def multiSourceToRelativeFlags (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    (ihom K).obj (((multiSEndofunctor r).obj ι).obj X).carrier ⟶
      suppliedMultiRelativeFlags supply r ι f hf K :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ ((ihom K).map (((multiSEndofunctor r).obj ι).map f).val) (by
    intro v
    obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K _).surjective v
    exact ⟨g ≫ multiSourceToWide supply r ι f hf, rfl⟩)

/-- 概要：始域から相対旗への射を含めると元の後合成そのものになる。
方針：全部分複体への持ち上げの包含公式。
規約：同型や置換後の比較で代用しない。
使われ方：実現後の比較が元の指定 K 射であることの照合。 -/
lemma multiSourceToRelativeFlags_inclusion (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    multiSourceToRelativeFlags supply r ι f hf K ≫
      multiRelativeFlagsInclusion r ι Y (multiWideStageData supply r ι f hf).subcomplex K =
      (ihom K).map (((multiSEndofunctor r).obj ι).map f).val := rfl

/-- 概要：相対旗の零段への始域射は元の同じ反復 S 射へ厳密に戻る。
方針：零段比較の包含と一点評価を計算する。
規約：別の完備化射や Kan 置換後の射で代用しない。
使われ方：元の K 射を含む相対比較の未置換零段の同定。 -/
lemma multiSourceToRelativeFlags_zero (supply : StableWideCofinalitySupply.{u})
    (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    multiSourceToRelativeFlags supply r ι f hf Δ[0] ≫
      (multiRelativeFlagZeroIso supply r ι f hf).hom =
    (pointFunctorEvaluationIso (((multiSEndofunctor r).obj ι).obj X).carrier).hom ≫
      (((multiSEndofunctor r).obj ι).map f).val := rfl

end SerrePositivity.KST.SConstruction.Cofinality
