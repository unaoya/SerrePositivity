module
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.KanContractibleBaseFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibrationInitialHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanLimits

/-! # 可縮な全空間の kernel pair と基点付きループ模型

概要：可縮な Kan 複体からの Kan fibration の自己引き戻しは底の基点付き左写像空間とホモトピー同値。
方針：自己引き戻しの第二射影の fiber へ戻し、元の fibration の fiber の表現可能な比較を使う。
規約：基点とホモトピー逆の選択を含む。使われ方：二枝の引き戻しをループ空間で読む。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：Kan fibration の自己引き戻しの第二射影も Kan fibration。
方針：ホーン持ち上げ性を引き戻す。
規約：両端自体の Kan 性は不要。使われ方：固定点上の fiber との比較。 -/
instance kanKernelPairProjection_fibration {E B : SSet.{u}} (r : E ⟶ B) [Fibration r] :
    Fibration (pullback.snd r r) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).2
  exact (MorphismProperty.rlp _).pullback_snd _ _
    ((SSet.modelCategoryQuillen.fibration_iff r).1 inferInstance)

/-- 概要：Kan 複体からの Kan fibration の自己引き戻しは Kan 複体。
方針：一方の脚の充填性と他方の始域の Kan 性を使う。
規約：底の Kan 性はこの段階では不要。使われ方：自己引き戻しの実際のホモトピー同値。 -/
instance kanKernelPair_kanComplex {E B : SSet.{u}} [KanComplex E]
    (r : E ⟶ B) [Fibration r] : KanComplex (pullback r r) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pullback_kanComplex_of_fibration r r

/-- 概要：可縮な全空間の自己引き戻しを第二射影の指定 fiber へ戻す射を選ぶ。
方針：可縮な底上の fiber 包含のホモトピー逆を選ぶ。
規約：逆射の選択を含む。使われ方：基点付きループ模型への実際の比較射。 -/
def kanKernelPairFiberRetraction {E B : SSet.{u}} [KanComplex E]
    (r : E ⟶ B) [Fibration r] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌) :
    pullback r r ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd r r) e :=
  Classical.choose (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberι_homotopyEquivalence_of_contractible_base (pullback.snd r r) hE e)

/-- 概要：選んだ戻し射は固定点の fiber を π₀ 上で恒等に戻す。
方針：fiber 包含と戻し射の合成のホモトピーを連結成分に移す。
規約：同じ基点と逆射の選択を使う。使われ方：ループ比較の固定 fiber 上の計算。 -/
lemma kanKernelPairFiberRetraction_piZero {E B : SSet.{u}} [KanComplex E]
    (r : E ⟶ B) [Fibration r] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd r r) e)) :
    SSet.mapπ₀ (kanKernelPairFiberRetraction r hE e)
      (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd r r) e) a) = a := by
  rw [← SSet.mapπ₀_comp_apply]
  have h := (Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberι_homotopyEquivalence_of_contractible_base (pullback.snd r r) hE e)).1.some
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.mapPiZero_eq_of_homotopy h a).trans (SSet.mapπ₀_id_apply _)

/-- 概要：選んだ固定 fiber への戻し射は単体的ホモトピー同値。
方針：元の fiber 包含を逆射に取り、二つの選択されたホモトピーを逆順に使う。
規約：π₀ の全単射だけでなく空間そのものの比較。使われ方：ループ模型への比較射の同値性。 -/
lemma kanKernelPairFiberRetraction_homotopyEquivalence {E B : SSet.{u}} [KanComplex E]
    (r : E ⟶ B) [Fibration r] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (kanKernelPairFiberRetraction r hE e) := by
  have h := Classical.choose_spec
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.vertexFiberι_homotopyEquivalence_of_contractible_base (pullback.snd r r) hE e)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd r r) e, h.2, h.1⟩

/-- 概要：自己引き戻しから底の基点付き左写像空間への実際の比較射。
方針：第二射影の fiber へ戻し、fiber の標準同型と始対象による表現可能な比較へ合成する。
規約：基点は r(e)。使われ方：二枝の引き戻しのループ表示。 -/
def kanKernelPairLoopComparison {E B : SSet.{u}} [KanComplex E]
    (r : E ⟶ B) [Fibration r] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌) :
    pullback r r ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft (r.app (Opposite.op ⦋0⦌) e) (r.app (Opposite.op ⦋0⦌) e) :=
  kanKernelPairFiberRetraction r hE e ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso r r e).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialHomComparison r e (hE.isInitialVertex e) (r.app (Opposite.op ⦋0⦌) e)

/-- 概要：可縮な Kan 複体からの Kan fibration の自己引き戻しは基点付きループ模型とホモトピー同値。
方針：戻し射、fiber の同型、表現可能な比較の三つの同値を合成する。
規約：底も Kan 複体とする。使われ方：交換作用とループ反転の比較の空間側。 -/
lemma kanKernelPairLoopComparison_homotopyEquivalence {E B : SSet.{u}}
    [KanComplex E] [KanComplex B] (r : E ⟶ B) [Fibration r]
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (kanKernelPairLoopComparison r hE e) := by
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd r r) e) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration _ _
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber r (r.app (Opposite.op ⦋0⦌) e)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration _ _
  have h₁ := (kanKernelPairFiberRetraction_homotopyEquivalence r hE e).isQCatEquivalence
  have h₂ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso r r e)).isQCatEquivalence
  have h₃ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialHomComparison_homotopyEquivalence r e
    (hE.isInitialVertex e) (r.app (Opposite.op ⦋0⦌) e)).isQCatEquivalence
  exact (h₁.comp (h₂.comp h₃)).isSimplicialHomotopyEquivalence

/-- 概要：自己引き戻しの連結成分は底の基点の自己射の型と同値。
方針：実際のループ比較の π₀ の同値と左模型の Hom 同値を合成する。
規約：底が Kan なので右辺は全て可逆な射である。使われ方：交換を逆射として読む準備。 -/
def kanKernelPairPiZeroLoopEquiv {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (r : E ⟶ B) [Fibration r] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌) :
    SSet.π₀ (pullback r r) ≃
      ((SSet.HomotopyCategory.mk (r.app (Opposite.op ⦋0⦌) e) : hoFunctor.obj B) ⟶
        SSet.HomotopyCategory.mk (r.app (Opposite.op ⦋0⦌) e)) :=
  (Equiv.ofBijective (SSet.mapπ₀ (kanKernelPairLoopComparison r hE e))
    (kanKernelPairLoopComparison_homotopyEquivalence r hE e).mapPiZero_bijective).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftPiZeroEquiv _ _)

/-- 概要：ループ比較は固定点の fiber 上で元の fibration の Hom 表示に一致する。
方針：包含後の戻し射の π₀ の式を使い、実際の比較射と Hom 同値の一致へ戻す。
規約：指定基点上の連結成分での計算則。使われ方：二枝交換の逆射との照合。 -/
lemma kanKernelPairPiZeroLoopEquiv_fiber {E B : SSet.{u}} [KanComplex E] [KanComplex B]
    (r : E ⟶ B) [Fibration r] (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan E) (e : E _⦋0⦌)
    (a : SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (pullback.snd r r) e)) :
    kanKernelPairPiZeroLoopEquiv r hE e (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd r r) e) a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv r e (hE.isInitialVertex e)
        (r.app (Opposite.op ⦋0⦌) e) (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberPullbackIso r r e).hom a) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeftPiZeroEquiv _ _ (SSet.mapπ₀ (kanKernelPairLoopComparison r hE e)
    (SSet.mapπ₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (pullback.snd r r) e) a)) = _
  simp only [kanKernelPairLoopComparison, SSet.mapπ₀_comp_apply]
  rw [kanKernelPairFiberRetraction_piZero]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftFibrationInitialFiberPiZeroEquiv_eq_comparison r e (hE.isInitialVertex e)
    (r.app (Opposite.op ⦋0⦌) e) _).symm

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
