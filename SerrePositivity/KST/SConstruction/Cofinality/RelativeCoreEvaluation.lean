module
public import SerrePositivity.KST.SConstruction.Cofinality.WideCompletionSupply
public import Mathlib.AlgebraicTopology.SimplicialSet.HoFunctorMonoidal

/-!
概要：同じ全多次数の相対 core 旗の評価を元の wide 部分複体と比較する。
方針：選択された部分複体を Sp-7 の具体的な全辺模型と同定し、水平辺と可逆辺を検査する。
規約：core 旗の実現と wide の亜群化を定義的に同一視しない。
使われ方：相対実現の自然な評価比較の構成。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：全多次数で選択した供給値は Sp-7 の具体的な全辺部分複体に等しい。
方針：両者の全単体条件を比較する。
規約：選択関数の計算や自然性を仮定しない。
使われ方：一般供給の離散性に加えて具体的な成分収縮を消費する。 -/
lemma completionMultiWide_eq (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex =
      LocalizingInvariants.completionCofiberWide (((multiSEndofunctor r).obj ι).map f).val := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  apply Subfunctor.ext
  funext n
  apply Set.ext
  intro s
  exact (multiWideStageData stableWideCofinalitySupply r ι f hf).simplex_spec n.unop.len s

/-- 概要：同じ多次数の相対 core 旗の元の全評価。
方針：core 包含と相対旗包含の後で内部 Hom の評価を行う。
規約：頂点だけの評価ではなく全パラメータ族の射を保持する。
使われ方：wide への評価の持ち上げ。 -/
def completionRelativeCoreEvaluation (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    K ⊗ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) : SSet.{u}) ⟶
      (((multiSEndofunctor r).obj ι).obj Y).carrier :=
  (K ◁ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore _).ι ≫ multiRelativeFlagsInclusion r ι Y
    (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex K)) ≫ (ihom.ev K).app _

/-- 概要：全多次数の元の可逆辺は、指定された cofiber 像条件を満たす。
方針：本質像とその安定閉包の等号を使い、可逆辺の零 cofiber を消費する。
規約：安定閉包への拡大を結論には残さない。
使われ方：相対 core 旗の評価の可逆な方向。 -/
lemma completionMulti_invertibleEdge_mem (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (a : (((multiSEndofunctor r).obj ι).obj Y).carrier _⦋1⦌)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a)) :
    a ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (LocalizingInvariants.completionEssentialImage
      (((multiSEndofunctor r).obj ι).map f).val) := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  have he := LocalizingInvariants.stableClosure_completionEssentialImage F.val
    (multiSEndofunctor_map_isIdempotentCompletion r ι f hf).2.1
  exact he ▸ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_of_isInvertible _ ha

/-- 概要：相対 core 旗の評価の水平辺は元の cofiber 像条件を満たす。
方針：旗全体の持ち上げを元の一辺で評価する。
規約：旗の辺ごとに持ち上げを選び直さない。
使われ方：評価の全 prism の分母所属。 -/
lemma completionRelativeCoreEvaluation_horizontal (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u})
    (a : K _⦋1⦌)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) : SSet.{u}) _⦋0⦌) :
    (completionRelativeCoreEvaluation r ι f hf K).app _
      (a, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
        (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) : SSet.{u}).σ 0 v) ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (LocalizingInvariants.completionEssentialImage
        (((multiSEndofunctor r).obj ι).map f).val) := by
  obtain ⟨g, hg⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v.val
  have he : (g.app (Opposite.op ⦋1⦌) a).val =
      (completionRelativeCoreEvaluation r ι f hf K).app _
        (a, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
          (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) : SSet.{u}).σ 0 v) :=
    congrArg (fun w => w.app (Opposite.op ⦋1⦌)
      (SimplexCategory.σ (0 : Fin 1)).op a) hg
  have hm := ((multiWideStageData stableWideCofinalitySupply r ι f hf).simplex_spec 1
    (g.app (Opposite.op ⦋1⦌) a).val).mp (g.app (Opposite.op ⦋1⦌) a).property (𝟙 ⦋1⦌)
  have hm' : (g.app (Opposite.op ⦋1⦌) a).val ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (LocalizingInvariants.completionEssentialImage
        (((multiSEndofunctor r).obj ι).map f).val) := by
    simpa only [LocalizingInvariants.completionEssentialImage, op_id,
      CategoryTheory.Functor.map_id, types_id_apply] using hm
  exact he ▸ hm'

/-- 概要：相対 core 旗の評価の可逆な方向も元の cofiber 像条件を満たす。
方針：core の一辺を頂点評価で写し、その可逆性から零 cofiber を使う。
規約：周囲の旗間の全射を可逆と仮定しない。
使われ方：評価の全 prism の分母所属。 -/
lemma completionRelativeCoreEvaluation_vertical (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u})
    (a : K _⦋0⦌)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) : SSet.{u}) _⦋1⦌) :
    (completionRelativeCoreEvaluation r ι f hf K).app _ (K.σ 0 a, v) ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (LocalizingInvariants.completionEssentialImage
        (((multiSEndofunctor r).obj ι).map f).val) := by
  let E := multiRelativeFlagsInclusion r ι Y
    (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex K ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (((multiSEndofunctor r).obj ι).obj Y).carrier) a
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge v).map E
  apply completionMulti_invertibleEdge_mem r ι f hf
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex v.val).map ((truncation 2).map E))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
      ((completionRelativeCoreEvaluation r ι f hf K).app _ (K.σ 0 a, v))) ?_).mp hi
  change v.val.val.app (Opposite.op ⦋1⦌) (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant a 1) =
    v.val.val.app (Opposite.op ⦋1⦌) (𝟙 _) (K.σ 0 a)
  exact congrArg (fun k => v.val.val.app (Opposite.op ⦋1⦌) (𝟙 _) k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one a)

/-- 概要：相対 core 旗の評価は全辺で元の cofiber 像条件を満たす。
方針：水平辺と可逆な垂直辺の実合成二単体へ分母の合成閉性を適用する。
規約：prism の斜辺も含め、頂点条件だけで代用しない。
使われ方：評価の wide 部分複体への持ち上げ。 -/
lemma completionRelativeCoreEvaluation_edges (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u})
    (s : (K ⊗ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) : SSet.{u})) _⦋1⦌) :
    (completionRelativeCoreEvaluation r ι f hf K).app _ s ∈
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberLocalizingEdges (LocalizingInvariants.completionEssentialImage
        (((multiSEndofunctor r).obj ι).map f).val) := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  let c := (Truncated.Edge.CompStruct.compId (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s.1)).tensor
    (Truncated.Edge.CompStruct.idComp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s.2))
  have ht := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberStableEdges_compStruct_twoOfThree
    (LocalizingInvariants.completionEssentialImage F.val)
    (c.map ((truncation 2).map (completionRelativeCoreEvaluation r ι f hf K)))
  rw [LocalizingInvariants.stableClosure_completionEssentialImage F.val
    (multiSEndofunctor_map_isIdempotentCompletion r ι f hf).2.1] at ht
  exact ht.1 (completionRelativeCoreEvaluation_horizontal r ι f hf K s.1 _)
    (completionRelativeCoreEvaluation_vertical r ι f hf K _ s.2)

/-- 概要：相対 core 旗の全評価は Sp-7 の元の wide 部分複体を経由する。
方針：評価の全辺条件を自然性で全単体へ移して持ち上げる。
規約：全ての高次単体を保持する厳密な因子化。
使われ方：相対 core 旗の実現から亜群化への評価比較。 -/
def completionRelativeCoreEvaluationWide (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    K ⊗ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) : SSet.{u}) ⟶
      (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val : SSet.{u}) :=
  Subcomplex.lift (completionRelativeCoreEvaluation r ι f hf K) (by
    intro n s hs
    obtain ⟨t, rfl⟩ := hs
    intro θ
    exact (ConcreteCategory.congr_hom
      ((completionRelativeCoreEvaluation r ι f hf K).naturality θ.op) t) ▸
      completionRelativeCoreEvaluation_edges r ι f hf K _)

/-- 概要：wide へ持ち上げた評価は包含後に元の全評価を厳密に回収する。
方針：部分複体への持ち上げの包含公式。
規約：置換後の射だけの比較に弱めない。
使われ方：元の相対図式との射の照合。 -/
lemma completionRelativeCoreEvaluationWide_inclusion (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    completionRelativeCoreEvaluationWide r ι f hf K ≫
      (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val).ι =
      completionRelativeCoreEvaluation r ι f hf K := rfl

/-- 概要：選択した全多次数の wide 模型は離散成分への実切断と全収縮を持つ。
方針：具体的な全辺模型との等号で Sp-7 の切断・収縮を移す。
規約：正次数の類の一意性だけに弱めず、元の未置換のホモトピーを保持する。
使われ方：相対旗の実現の収縮を構成するための実データ。 -/
theorem completionMultiWide_componentRetraction (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    ∃ (T : Type u)
      (p : ((multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex : SSet.{u}) ⟶
        (Functor.const SimplexCategoryᵒᵖ).obj T)
      (s : (Functor.const SimplexCategoryᵒᵖ).obj T ⟶
        ((multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex : SSet.{u})),
      s ≫ p = 𝟙 _ ∧ Nonempty (SSet.Homotopy (p ≫ s) (𝟙 _)) := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  have hF := multiSEndofunctor_map_isIdempotentCompletion r ι f hf
  have hS := congrArg (fun M :
    (((multiSEndofunctor r).obj ι).obj Y).carrier.Subcomplex => (M : SSet.{u}))
    (completionMultiWide_eq r ι f hf)
  rw [hS]
  exact ⟨_, LocalizingInvariants.completionComponentProjection F.val,
    LocalizingInvariants.completionComponentSection F.val hF,
    LocalizingInvariants.completionComponentSection_projection F.val hF,
    ⟨LocalizingInvariants.completionWideContraction F.val hF⟩⟩

end SerrePositivity.KST.SConstruction.Cofinality
