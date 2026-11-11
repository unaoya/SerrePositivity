module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SubterminalRelativeFunctor
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanInvertible
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithfulEquivalence

/-!
概要：一点を底とする left fibrations の ∞ 圏と 𝒮 の、fiber 評価による同値。
方針：相対 Hom の厳密な同型による充満忠実性と、任意の Kan 複体を全空間とする射影の構成を使う。
規約：一般の底に対する straightening の同値は別に証明する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の分類の値での比較を支える一点上の同値。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：各次数で高々一点の底への Kan 複体からの射は left fibration。
方針：Kan のホーン充填を選び、底の可換性は各単体の一意性で示す。
規約：射は定値射に限らない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一点上の left fibration として任意の Kan 複体を実現する。 -/
instance leftFibration_to_subterminal_of_kan {E B : SSet.{u}} [KanComplex E]
    [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (p : E ⟶ B) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p where
  mem := by
    intro A D i hi
    cases hi with
    | @intro n k hk =>
      constructor
      intro a b sq
      obtain ⟨H, hH⟩ := KanComplex.hornFilling a
      refine CommSq.HasLift.mk' { l := H, fac_left := hH.symm, fac_right := ?_ }
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro x
      exact Subsingleton.elim _ _

/-- 概要：一点を底とする left fibrations の fiber 評価は本質的全射。
方針：各 𝒮 の頂点が表す Kan 複体から定値射影を作り、fiber の包含の同型で比較する。
規約：任意の coherent な頂点を元の KanObject に戻して扱う。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一点上の分類の対象での全射性。 -/
lemma leftFibrationInfinityFiberEvaluation_isEssentiallySurjective_of_subterminal
    {B : SSet.{u}} [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b) := by
  intro y
  let K : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u} := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject y
  let p : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationObject B := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationObjectOf (SSet.const b : K.obj ⟶ B)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex p, ?_⟩
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation_vertex]
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.vertexFiberSubterminalBaseIso (SSet.const b : K.obj ⟶ B) b
  have hf : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationFiberObject b p ⟶ K from e.hom) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso e).isQCatEquivalence
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (show _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationFiberObject b p ⟶ K from e.hom)
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence hf
  let : IsIso (SSet.Truncated.HomotopyCategory.homMk a.toTruncated) := ha
  exact ⟨asIso (SSet.Truncated.HomotopyCategory.homMk a.toTruncated) ≪≫
    eqToIso (congrArg SSet.HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object y))⟩

/-- 概要：一点を底とする left fibrations の fiber 評価は quasicategory の同値。
方針：写像空間での充満忠実性と対象での本質的全射性を同値判定に適用する。
規約：順方向は既存の fiber 評価関手そのもの。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、分類の一点を底とする場合の実際の同値。 -/
lemma leftFibrationInfinityFiberEvaluation_isQCatEquivalence_of_subterminal
    {B : SSet.{u}} [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation b) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationInfinityFiberEvaluation_isFullyFaithful_of_subterminal b)
    (leftFibrationInfinityFiberEvaluation_isEssentiallySurjective_of_subterminal b)

/-- 概要：一点上の left fibrations と 𝒮 の fiber 評価を順方向とする同値データ。
方針：証明した同値性から逆射と二つの可逆な関手間の比較を取り出す。
規約：一般の底の straightening の単位・余単位はこの定義では主張しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、写像空間の値での比較に用いる一点上の逆データ。 -/
noncomputable def leftFibrationInfinitySubterminalEquivalence
    {B : SSet.{u}} [∀ n : SimplexCategoryᵒᵖ, Subsingleton (B.obj n)] (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity B) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} :=
  (leftFibrationInfinityFiberEvaluation_isQCatEquivalence_of_subterminal b).choose

/-- 概要：標準零単体を底とする left fibrations の ∞ 圏は 𝒮 と同値。
方針：唯一の頂点での fiber 評価の同値を標準零単体へ適用する。
規約：順方向の評価の対象は u の Kan fiber、同値の宇宙は u+1。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、一般の straightening の値での同値の基礎。 -/
noncomputable def leftFibrationInfinityPointEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftFibrationInfinity (Δ[0] : SSet.{u})) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} := by
  letI (n : SimplexCategoryᵒᵖ) : Subsingleton ((Δ[0] : SSet.{u}).obj n) := ⟨fun x y ↦ by
    apply stdSimplex.ext
    intro i
    apply Fin.ext
    omega⟩
  exact leftFibrationInfinitySubterminalEquivalence (stdSimplex.obj₀Equiv.symm (0 : Fin 1))

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
