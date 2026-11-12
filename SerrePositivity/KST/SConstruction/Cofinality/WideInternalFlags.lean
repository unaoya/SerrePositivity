module
public import SerrePositivity.KST.SConstruction.Cofinality.RelativeFlagDiagonalEvaluation

/-!
概要：同じ全多次数の wide 内部旗から ambient 相対旗への具体的な比較を構成する。
方針：全辺模型の包含で後合成し、選択された模型との等号で頂点条件を確認する。
規約：一般 core 旗の弱同値性をここでは証明せず、相対側の射を固定する。
使われ方：Sp-8 の対角評価を相対旗の評価へ接続する入力。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：元の wide 模型の内部旗は同じ ambient 相対旗を定める。
方針：包含による後合成を全部分圏へ持ち上げる。
規約：同じ指定完備化射と全多次数を保持する。
使われ方：内部旗と相対旗の core 比較の順方向。 -/
def completionWideToRelativeFlags (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    (ihom K).obj (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) ⟶
      suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift _ ((ihom K).map
    (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val).ι) (by
    intro v
    obtain ⟨g, rfl⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K _).surjective v
    let hM := (completionMultiWide_eq r ι f hf).symm.le
    refine ⟨g ≫ Subcomplex.homOfLE hM, ?_⟩
    exact congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((Category.assoc g _ _).trans
      (congrArg (fun q => g ≫ q) (Subcomplex.homOfLE_ι hM))))

/-- 概要：内部旗の比較は包含後に元の wide 包含による後合成となる。
方針：全部分圏への持ち上げの定義を計算する。
規約：未置換の射の等号。
使われ方：元の評価射との照合。 -/
lemma completionWideToRelativeFlags_inclusion (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    completionWideToRelativeFlags r ι f hf K ≫ multiRelativeFlagsInclusion r ι Y
      (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex K =
      (ihom K).map (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val).ι := rfl

/-- 概要：内部旗の比較は任意のパラメータ前合成と厳密に可換。
方針：部分型の元の値に戻して前合成と後合成の可換性を計算する。
規約：単体の面だけでなく任意のパラメータ射を扱う。
使われ方：旗方向の単体的比較。 -/
lemma completionWideToRelativeFlags_precomp (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) {L K : SSet.{u}} (i : L ⟶ K) :
    (pre i).app (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) ≫
      completionWideToRelativeFlags r ι f hf L =
      completionWideToRelativeFlags r ι f hf K ≫ multiRelativeFlagsPrecomp r ι Y
        (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex i := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro v
  apply Subtype.ext
  rfl

/-- 概要：同じ全多次数の具体的な wide 模型の core 内部旗図式。
方針：標準単体の前合成と内部 Hom、core を順に合成する。
規約：一般供給の正本を複製せず、この指定射の入力だけを定める。
使われ方：Sp-8 の評価弱同値を明示的な引数として受ける始域。 -/
def completionWideCoreFlagDiagram (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) : SimplexCategoryᵒᵖ ⥤ SSet.{u} :=
  (SSet.stdSimplex.op ⋙ internalHom ⋙ (evaluation SSet SSet).obj
    (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor

/-- 概要：内部 core 旗の比較を旗方向の自然変換に束ねる。
方針：既存の前合成可換性へ core 関手を適用する。
規約：相対側は同じ全多次数の元の相対旗を使う。
使われ方：対角実現の比較射。 -/
def completionWideCoreFlagComparison (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionWideCoreFlagDiagram r ι f ⟶ completionRelativeCoreFlagDiagram r ι f hf where
  app n := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap
    (completionWideToRelativeFlags r ι f hf (SSet.stdSimplex.obj n.unop))
  naturality {n m} α := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map _ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map _
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map_comp _ _).symm.trans
      ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map
        (completionWideToRelativeFlags_precomp r ι f hf (SSet.stdSimplex.map α.unop))).trans
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.map_comp _ _))

/-- 概要：内部 core 旗の対角を元の相対旗の対角へ写す。
方針：旗図式の自然変換に対角関手を適用する。
規約：Kan 置換を介さず元の対角の射を構成する。
使われ方：一般評価と相対評価の接続。 -/
def completionWideFlagDiagonalComparison (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    simplicialDiagonalFunctor.obj (completionWideCoreFlagDiagram r ι f) ⟶
      completionRelativeFlagRealization r ι f hf :=
  simplicialDiagonalFunctor.map (completionWideCoreFlagComparison r ι f hf)

/-- 概要：内部 core 旗の評価は相対評価との合成で元の対角制限を回収する。
方針：部分型の値と内部 Hom の評価を定義どおりに計算する。
規約：包含後の弱い照合ではなく wide 模型内での全単体の等号。
使われ方：Sp-8 の評価弱同値を受け取る際の式。 -/
lemma completionWideFlagDiagonalComparison_evaluation (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (n : ℕ)
    (v : (simplicialDiagonalFunctor.obj (completionWideCoreFlagDiagram r ι f)) _⦋n⦌) :
    (completionWideFlagDiagonalComparison r ι f hf ≫
      completionRelativeFlagWideEvaluation r ι f hf).app (Opposite.op ⦋n⦌) v =
      SSet.yonedaEquiv (CartesianMonoidalCategory.lift (𝟙 (Δ[n] : SSet.{u})) (𝟙 _) ≫
        uncurry (SSet.yonedaEquiv.symm v.val)) := by
  apply Subtype.ext
  rfl

/-- 概要：一般評価の供給を明示的に受け取り、相対評価へ弱同値性を移す。
方針：対角制限の厳密な照合と弱同値の二対三則を使う。
規約：一般評価と内部旗比較の弱同値性はそれぞれ明示的な引数である。
使われ方：Sp-8 を待つ間の、未証明の比較条件を正確に分離した接続。 -/
lemma completionRelativeFlagWideEvaluation_isWeak_of_coreFlag (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (ε : simplicialDiagonalFunctor.obj (completionWideCoreFlagDiagram r ι f) ⟶
      (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}))
    (hε : ∀ (n : ℕ)
      (v : (simplicialDiagonalFunctor.obj (completionWideCoreFlagDiagram r ι f)) _⦋n⦌),
      ε.app (Opposite.op ⦋n⦌) v =
        SSet.yonedaEquiv (CartesianMonoidalCategory.lift (𝟙 (Δ[n] : SSet.{u})) (𝟙 _) ≫
          uncurry (SSet.yonedaEquiv.symm v.val)))
    (hweak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence ε)
    (hcomparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (completionWideFlagDiagonalComparison r ι f hf)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (completionRelativeFlagWideEvaluation r ι f hf) := by
  have he : completionWideFlagDiagonalComparison r ι f hf ≫
      completionRelativeFlagWideEvaluation r ι f hf = ε := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    exact (completionWideFlagDiagonalComparison_evaluation r ι f hf n.unop.len v).trans
      (hε n.unop.len v).symm
  exact hcomparison.cancel_left (he.symm ▸ hweak)

end SerrePositivity.KST.SConstruction.Cofinality
