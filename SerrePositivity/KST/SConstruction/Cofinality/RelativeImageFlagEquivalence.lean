module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagVertexRecovery
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.CoreEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceStability

/-!
概要：相対旗の指定頂点が像に入る全部分圏を、元の始域の全旗圏と同定する。
方針：同じ相対旗への射の充満忠実性と像成分の頂点回収を合わせる。
規約：この全部分圏を実現後のホモトピー fiber と未証明のまま同一視しない。
使われ方：相対 S• 比較の始域側の圏同値。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：指定した一頂点の像所属条件を相対旗へ課す全部分圏。
方針：元の反復 S 射の本質像を指定頂点で評価する。
規約：retract 閉包へ広げず、周囲の全高次単体を保つ。
使われ方：元の始域と比較する相対旗の部分。 -/
def completionRelativeImageFlags (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) {K : SSet.{u}}
    (k₀ : K _⦋0⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices
    (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K)
    (fun v => (completionRelativeFlagVertexFunctor r ι f hf v).app (Opposite.op ⦋0⦌) k₀ ∈
      LocalizingInvariants.completionEssentialImage (((multiSEndofunctor r).obj ι).map f).val)

instance completionRelativeImageFlags_quasicategory (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) {K : SSet.{u}} (k₀ : K _⦋0⦌) :
    Quasicategory (completionRelativeImageFlags r ι f hf k₀) := by
  unfold completionRelativeImageFlags
  infer_instance

/-- 概要：元の始域の全旗を相対旗の指定像部分へ送る。
方針：元の相対旗射に、その像の頂点評価の所属を添える。
規約：包含後は指定された元の旗の射を保持する。
使われ方：始域の全旗圏との同値の順方向。 -/
def completionSourceImageFlagMap (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) {K : SSet.{u}} (k₀ : K _⦋0⦌) :
    (ihom K).obj (((multiSEndofunctor r).obj ι).obj X).carrier ⟶
      completionRelativeImageFlags r ι f hf k₀ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (multiSourceToRelativeFlags stableWideCofinalitySupply r ι f hf K)
    (fun s => completionSourceFlagVertexIso_image r ι f hf s _ (Iso.refl _) k₀)

/-- 概要：始域の旗から指定像部分への元の射は充満忠実。
方針：全部分圏の包含で反映し、元の相対旗射の充満忠実性を使う。
規約：関手の順方向を変更しない。
使われ方：始域側の旗圏同値の局所条件。 -/
lemma completionSourceImageFlagMap_isFullyFaithful (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) {K : SSet.{u}} (k₀ : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (completionSourceImageFlagMap r ι f hf k₀) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).cancel_right
  exact completionSourceToRelativeFlags_isFullyFaithful r ι f hf K

/-- 概要：連結なパラメータでは指定像部分の全ての旗を元の始域から回収できる。
方針：相対旗内の回収同型を像部分の全包含で反映する。
規約：各頂点の同型を一つの相対旗圏内で保持する。
使われ方：始域側の旗圏同値の大域条件。 -/
lemma completionSourceImageFlagMap_isEssentiallySurjective (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {K : SSet.{u}} [K.IsPreconnected] (k₀ : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (completionSourceImageFlagMap r ι f hf k₀) := by
  intro v
  obtain ⟨s, ⟨e⟩⟩ := exists_completionSourceFlagVertexIso r ι f hf v.val k₀
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v)
  let I : completionRelativeImageFlags r ι f hf k₀ ⟶
      suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ (fun v =>
      (completionRelativeFlagVertexFunctor r ι f hf v).app (Opposite.op ⦋0⦌) k₀ ∈
        LocalizingInvariants.completionEssentialImage
          (((multiSEndofunctor r).obj ι).map f).val)).ι
  have hI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful I := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _
  exact ⟨s, ⟨hI.preimageVertexIso e⟩⟩

/-- 概要：連結パラメータの相対旗の指定像部分は元の始域の全旗圏と同値。
方針：元の射の充満忠実性と本質全射性から明示的な逆データを得る。
規約：この圏同値だけから実現後の fiber 比較は結論しない。
使われ方：相対 S• の始域側の同定。 -/
def completionRelativeImageFlagEquivalence (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {K : SSet.{u}} [K.IsPreconnected] (k₀ : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((ihom K).obj (((multiSEndofunctor r).obj ι).obj X).carrier)
      (completionRelativeImageFlags r ι f hf k₀) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.qCatEquivalenceOfFullyFaithfulEssentiallySurjective
    (completionSourceImageFlagMap r ι f hf k₀)
    (completionSourceImageFlagMap_isFullyFaithful r ι f hf k₀)
    (completionSourceImageFlagMap_isEssentiallySurjective r ι f hf k₀)

/-- 概要：連結な旗の指定像部分は元の始域の安定性を持つ。
方針：全旗圏の安定性を構成した圏同値で移す。
規約：周囲の相対旗全体の安定性はここでは主張しない。
使われ方：始域側の S 構成を比較に適用する入口。 -/
instance completionRelativeImageFlags_isStable (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {K : SSet.{u}} [K.IsPreconnected] (k₀ : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (completionRelativeImageFlags r ι f hf k₀) :=
  (completionRelativeImageFlagEquivalence r ι f hf k₀).isStable_iff.mp inferInstance

/-- 概要：元の始域から指定像部分への core 射そのものが同値となる。
方針：指定された順方向の充満忠実・本質全射な射の同値性を core へ移す。
規約：独立に選んだ core 比較射へ置き換えない。
使われ方：相対 S• 実現の始域側の行比較。 -/
lemma completionSourceImageFlagMap_core_isQCatEquivalence (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    {K : SSet.{u}} [K.IsPreconnected] (k₀ : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (completionSourceImageFlagMap r ι f hf k₀)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective
    (completionSourceImageFlagMap r ι f hf k₀)
    (completionSourceImageFlagMap_isFullyFaithful r ι f hf k₀)
    (completionSourceImageFlagMap_isEssentiallySurjective r ι f hf k₀)).core

end SerrePositivity.KST.SConstruction.Cofinality
