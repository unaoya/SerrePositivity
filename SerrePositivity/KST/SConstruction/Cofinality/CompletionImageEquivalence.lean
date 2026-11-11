module
public import SerrePositivity.KST.SConstruction.Cofinality.CompletionImageClosed
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceStability
public import SerrePositivity.KST.SConstruction.StableModelEquivalences

/-!
概要：同じ全多次数の元の始域を、閉じた本質像の安定模型と同定する。
方針：元の指定射を本質像へ制限し、充満忠実性と頂点同型の回収を使う。
規約：順方向の射は包含後に元の指定射へ厳密に戻る。
使われ方：K-B2-S1 の左項を元の始域の K 値へ戻す比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の同じ反復 S 射を、その閉じた本質像へ制限する。
方針：元の像頂点には恒等同型による所属証拠を添える。
規約：主経路の始域に完備性を追加しない。
使われ方：元の始域と本質像の圏同値の順射。 -/
def completionSourceToImage (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (((multiSEndofunctor r).obj ι).obj X).carrier ⟶
      closedSubcategory (completionImageClosedPredicate r ι f hf) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ (((multiSEndofunctor r).obj ι).map f).val
    (fun x => ⟨x, ⟨Iso.refl _⟩⟩)

/-- 概要：本質像への制限は包含後に元の反復 S 射を厳密に回収する。
方針：全部分圏への持ち上げの定義を計算する。
規約：元の射を独立な同値へ置き換えない。
使われ方：fiber 比較の左射を元の K 射へ接続する。 -/
lemma completionSourceToImage_inclusion (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionSourceToImage r ι f hf ≫
      (closedStableInclusion (completionImageClosedPredicate r ι f hf)).val =
      (((multiSEndofunctor r).obj ι).map f).val := rfl

/-- 概要：本質像への元の制限射は充満忠実。
方針：全部分圏の包含を消去して元の完備化射の充満忠実性へ戻す。
規約：同じ全多次数の元の射を扱う。
使われ方：本質像比較の局所条件。 -/
lemma completionSourceToImage_isFullyFaithful (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (completionSourceToImage r ι f hf) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _).cancel_right
  exact (multiSEndofunctor_map_isIdempotentCompletion r ι f hf).2.1

/-- 概要：閉じた本質像の全頂点を元の始域から同型で回収できる。
方針：本質像の所属証拠を取り出し、全部分圏の充満忠実性で同型を戻す。
規約：周囲の同型を本質像内部の同型として保持する。
使われ方：本質像比較の大域条件。 -/
lemma completionSourceToImage_isEssentiallySurjective (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (completionSourceToImage r ι f hf) := by
  intro v
  obtain ⟨x, ⟨e⟩⟩ := closedSubcategory_vertex (completionImageClosedPredicate r ι f hf) v
  let I := (closedStableInclusion (completionImageClosedPredicate r ι f hf)).val
  have hI : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful I := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _
  exact ⟨x, ⟨hI.preimageVertexIso e⟩⟩

/-- 概要：元の始域と閉じた本質像の全高次圏は同値。
方針：指定された元の制限射の充満忠実性と本質全射性を束ねる。
規約：順射は元の指定反復 S 射を保持する。
使われ方：相対 fiber 供給の左項を元の始域へ戻す。 -/
def completionSourceImageEquivalence (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (((multiSEndofunctor r).obj ι).obj X).carrier
      (closedSubcategory (completionImageClosedPredicate r ι f hf)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.qCatEquivalenceOfFullyFaithfulEssentiallySurjective (completionSourceToImage r ι f hf)
    (completionSourceToImage_isFullyFaithful r ι f hf)
    (completionSourceToImage_isEssentiallySurjective r ι f hf)

/-- 概要：元の始域から閉じた本質像への制限を完全関手として束ねる。
方針：同じ順射の圏同値から完全性を得る。
規約：包含後に元の指定射を保持する。
使われ方：K-B2-S1 の左項と元の始域の間の K 比較。 -/
def completionSourceImageStableMap (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    ((multiSEndofunctor r).obj ι).obj X ⟶
      closedStableModel (completionImageClosedPredicate r ι f hf) := by
  let e := completionSourceImageEquivalence r ι f hf
  have hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  exact ⟨e.hom, @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ _ e.hom hE,
    fun t ht => @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber _ _ e.hom hE t ht⟩

/-- 概要：元の始域と閉じた本質像は、元の制限射を順射とする安定模型の同値。
方針：逆射の完全性を圏同値から得て、元の二つの関手同型を保持する。
規約：本質像の模型に新たな完備性を仮定しない。
使われ方：既存の S• 同値不変性への代入。 -/
def completionSourceImageStableEquivalence (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    StableModelEquivalence (((multiSEndofunctor r).obj ι).obj X)
      (closedStableModel (completionImageClosedPredicate r ι f hf)) := by
  let e := completionSourceImageEquivalence r ι f hf
  have hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact ⟨completionSourceImageStableMap r ι f hf,
    ⟨e.inv, @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero _ _ e.inv hE,
      fun t ht => @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber _ _ e.inv hE t ht⟩,
    e.homInvIso, e.invHomIso⟩

/-- 概要：本質像への制限と閉じた部分圏の包含の合成は元の反復 S 射。
方針：元の単体集合の射の厳密な包含公式へ戻す。
規約：安定模型の射の等号として保持する。
使われ方：実現後に元の指定 K 射へ戻す照合。 -/
lemma completionSourceImageStableMap_inclusion (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionSourceImageStableMap r ι f hf ≫
      closedStableInclusion (completionImageClosedPredicate r ι f hf) =
      ((multiSEndofunctor r).obj ι).map f := by
  apply Subtype.ext
  exact completionSourceToImage_inclusion r ι f hf

end SerrePositivity.KST.SConstruction.Cofinality
