module
public import SerrePositivity.KST.SConstruction.Cofinality.WideComponentBar
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopyInverse

/-!
概要：元の全辺 wide 模型から元の離散成分への射影を保持する。
方針：Sp-7 の同じ射影・切断・実収縮を使って弱同値性を得る。
規約：成分ごとの切断の選択の自然性は要求しない。
使われ方：全 S 多次数の相対旗から障害成分への自然な離散化。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の全辺 wide 模型から元の成分集合への定値射影。
方針：Sp-7 の元の射影を同じ多次数で使う。
規約：切断の選択を射影の定義へ持ち込まない。
使われ方：相対旗の自然な離散化の後半。 -/
def completionCanonicalComponentProjection (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) :
    (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj (SSet.π₀
        (LocalizingInvariants.completionCofiberWide
          (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) :=
  LocalizingInvariants.completionComponentProjection (((multiSEndofunctor r).obj ι).map f).val

/-- 概要：元の離散成分への射影は弱ホモトピー同値。
方針：Sp-7 の同じ切断と実収縮をホモトピー逆の証拠へ渡す。
規約：選択した切断の全多次数での自然性は不要。
使われ方：離散化の次数ごとの弱同値性。 -/
lemma completionCanonicalComponentProjection_isWeak (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (completionCanonicalComponentProjection r ι f) := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  have hF := multiSEndofunctor_map_isIdempotentCompletion r ι f hf
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence
  refine ⟨LocalizingInvariants.completionComponentSection F.val hF,
    ⟨LocalizingInvariants.completionWideContraction F.val hF⟩, ?_⟩
  change Nonempty (SSet.Homotopy
    (LocalizingInvariants.completionComponentSection F.val hF ≫
      LocalizingInvariants.completionComponentProjection F.val) (𝟙 _))
  rw [LocalizingInvariants.completionComponentSection_projection F.val hF]
  exact ⟨SSet.RelativeMorphism.Homotopy.refl (SSet.RelativeMorphism.botEquiv.symm (𝟙 _))⟩

/-- 概要：元の成分射影は全 S 多次数の元の構造射で自然。
方針：成分ラベル写像の一般前合成公式を使う。
規約：自然性を切断の選択から導かない。
使われ方：元の全多次数の離散成分図式への自然変換。 -/
lemma completionCanonicalComponentProjection_naturality (r : ℕ)
    {ι κ : Fin r → SimplexCategoryᵒᵖ} (α : ι ⟶ κ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionCanonicalWideStructureMap r α f hf ≫ completionCanonicalComponentProjection r κ f =
      completionCanonicalComponentProjection r ι f ≫ (Functor.const SimplexCategoryᵒᵖ).map
        (↾(SSet.mapπ₀ (completionCanonicalWideStructureMap r α f hf))) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentLabelMap_pre (completionCanonicalWideStructureMap r α f hf) id

end SerrePositivity.KST.SConstruction.Cofinality
