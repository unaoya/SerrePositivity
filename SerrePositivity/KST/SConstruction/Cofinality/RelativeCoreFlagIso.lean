module
public import SerrePositivity.KST.SConstruction.Cofinality.WideInvertibleReflection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalencePathInternalHom

/-!
概要：同じ全多次数の内部 wide 旗と相対旗の core を比較する。
方針：相対 core の全評価を curry し、点ごとの可逆性を wide 内へ反映する。
規約：一般 core 旗の対角弱同値は外部供給に残す。
使われ方：Sp-8 の供給を消費する相対側の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：相対 core 旗を同じ wide 模型の内部 core 旗へ戻す。
方針：全評価の curry の可逆性を各頂点で検査する。
規約：ambient での可逆性を wide 内へ反映する補題を使う。
使われ方：core 旗比較の逆射。 -/
def completionRelativeCoreToWideFlags (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
      (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) : SSet.{u}) ⟶
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj (LocalizingInvariants.completionCofiberWide
        (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) : SSet.{u}) := by
  let F := ((multiSEndofunctor r).obj ι).map f
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor F.val := stableModelHom_exact F
  let : Quasicategory (LocalizingInvariants.completionCofiberWide F.val : SSet.{u}) :=
    LocalizingInvariants.completionCofiberWide_quasicategory F.val
      (multiSEndofunctor_map_isIdempotentCompletion r ι f hf)
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreLift (curry (completionRelativeCoreEvaluationWide r ι f hf K)) ?_
  intro s
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_iff_evaluateFunctorAt_any _).mpr
  intro k
  let a := ((curry (completionRelativeCoreEvaluationWide r ι f hf K)) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k).app (Opposite.op ⦋1⦌) s
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a)
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((curry (completionRelativeCoreEvaluationWide r ι f hf K)).app
      (Opposite.op ⦋1⦌) s)).map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k))) rfl).mp
  apply completionWide_invertibleEdge_of_ambient r ι f hf a
  let E := multiRelativeFlagsInclusion r ι Y
    (multiWideStageData stableWideCofinalitySupply r ι f hf).subcomplex K ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := (((multiSEndofunctor r).obj ι).obj Y).carrier) k
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore_edge s).map E
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex s.val).map ((truncation 2).map E))
    (f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex a.val) rfl).mp h

/-- 概要：内部旗から相対旗へ移して戻すと元の core 旗を厳密に回収する。
方針：core と wide の部分型を外し、内部 Hom の全評価を計算する。
規約：同値の存在だけでなく、指定された比較射の逆である。
使われ方：core 旗比較の同型の一方の逆則。 -/
lemma completionWideRelativeCore_roundtrip (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (completionWideToRelativeFlags r ι f hf K) ≫
      completionRelativeCoreToWideFlags r ι f hf K = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro v
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro m θ
  apply ConcreteCategory.hom_ext
  intro k
  apply Subtype.ext
  change (v.val.app m (θ ≫ 𝟙 m) k).val = (v.val.app m θ k).val
  rw [Category.comp_id]

/-- 概要：相対 core 旗を内部旗へ移して戻すと元の相対旗を厳密に回収する。
方針：二つの包含の後で全評価を計算する。
規約：像の頂点だけでなく全高次単体の逆則。
使われ方：core 旗比較の同型のもう一方の逆則。 -/
lemma completionRelativeWideCore_roundtrip (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    completionRelativeCoreToWideFlags r ι f hf K ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (completionWideToRelativeFlags r ι f hf K) = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro v
  apply Subtype.ext
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro m θ
  apply ConcreteCategory.hom_ext
  intro k
  change v.val.val.app m (θ ≫ 𝟙 m) k = v.val.val.app m θ k
  rw [Category.comp_id]

/-- 概要：同じ全多次数の wide 内部旗と相対旗の core は厳密に同型。
方針：指定比較射と全評価から構成した逆射を二つの逆則で束ねる。
規約：一般 core 旗の評価弱同値は使わない。
使われ方：一般供給と相対実現の間の S• 固有の比較。 -/
def completionWideRelativeCoreIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) (K : SSet.{u}) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})) : SSet.{u}) ≅
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore
        (suppliedMultiRelativeFlags stableWideCofinalitySupply r ι f hf K) : SSet.{u}) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap (completionWideToRelativeFlags r ι f hf K)
  inv := completionRelativeCoreToWideFlags r ι f hf K
  hom_inv_id := completionWideRelativeCore_roundtrip r ι f hf K
  inv_hom_id := completionRelativeWideCore_roundtrip r ι f hf K

/-- 概要：内部 core 旗と相対 core 旗の同型は旗方向で自然である。
方針：指定比較射の前合成可換性と各段の厳密な逆を束ねる。
規約：同じ全多次数を固定する。
使われ方：対角関手を適用する前の自然同型。 -/
def completionWideRelativeCoreDiagramIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    completionWideCoreFlagDiagram r ι f ≅ completionRelativeCoreFlagDiagram r ι f hf :=
  NatIso.ofComponents (fun n =>
    completionWideRelativeCoreIso r ι f hf (SSet.stdSimplex.obj n.unop))
      (fun α => (completionWideCoreFlagComparison r ι f hf).naturality α)

/-- 概要：内部 core 旗と相対 core 旗の対角比較は同型である。
方針：旗方向の自然同型へ対角関手を適用する。
規約：相対評価射そのものの弱同値性とは分離する。
使われ方：一般評価の供給を相対評価へ移す。 -/
def completionWideRelativeFlagDiagonalIso (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    simplicialDiagonalFunctor.obj (completionWideCoreFlagDiagram r ι f) ≅
      completionRelativeFlagRealization r ι f hf :=
  simplicialDiagonalFunctor.mapIso (completionWideRelativeCoreDiagramIso r ι f hf)

/-- 概要：指定した内部旗から相対旗への対角射は弱ホモトピー同値。
方針：同じ射を厳密な同型の順射として表示する。
規約：一般 core 旗の評価弱同値は使わない。
使われ方：Sp-8 消費に残っていた相対側の比較条件を消去する。 -/
lemma completionWideFlagDiagonalComparison_isWeak (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (completionWideFlagDiagonalComparison r ι f hf) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (completionWideRelativeFlagDiagonalIso r ι f hf)).isWeakHomotopyEquivalence

/-- 概要：一般 core 旗評価の供給を、この指定射の wide 模型で受け取る型。
方針：評価射、対角制限との等号、その弱同値性を明示的にまとめる。
規約：未到着の一般定理を公理や instance として登録しない。
使われ方：Sp-8 の公開 API を代入する相対側の入口。 -/
structure CompletionCoreFlagEvaluationInput (r : ℕ) (ι : Fin r → SimplexCategoryᵒᵖ)
    {X Y : StableModel.{u}} (f : X ⟶ Y) where
  evaluation : simplicialDiagonalFunctor.obj (completionWideCoreFlagDiagram r ι f) ⟶
    (LocalizingInvariants.completionCofiberWide
      (((multiSEndofunctor r).obj ι).map f).val : SSet.{u})
  diagonal_eq : ∀ (n : ℕ)
    (v : (simplicialDiagonalFunctor.obj (completionWideCoreFlagDiagram r ι f)) _⦋n⦌),
    evaluation.app (Opposite.op ⦋n⦌) v =
      SSet.yonedaEquiv (CartesianMonoidalCategory.lift (𝟙 (Δ[n] : SSet.{u})) (𝟙 _) ≫
        uncurry (SSet.yonedaEquiv.symm v.val))
  isWeak : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence evaluation

/-- 概要：一般 core 旗評価の供給があれば、元の相対旗の wide 評価は弱同値。
方針：内部旗との厳密な同型と、対角制限の照合を使う。
規約：残る一般供給だけを明示的な仮定引数として保持する。
使われ方：相対実現の離散性と fiber 比較へ進むための条件付き接続。 -/
lemma completionRelativeFlagWideEvaluation_isWeak_of_input (r : ℕ)
    (ι : Fin r → SimplexCategoryᵒᵖ) {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (input : CompletionCoreFlagEvaluationInput r ι f) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (completionRelativeFlagWideEvaluation r ι f hf) :=
  completionRelativeFlagWideEvaluation_isWeak_of_coreFlag r ι f hf input.evaluation
    input.diagonal_eq input.isWeak (completionWideFlagDiagonalComparison_isWeak r ι f hf)

end SerrePositivity.KST.SConstruction.Cofinality
