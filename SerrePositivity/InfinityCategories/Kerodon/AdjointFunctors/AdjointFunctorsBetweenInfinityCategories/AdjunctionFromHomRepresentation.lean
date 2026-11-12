module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.CouplingsOfInfinityCategories.AdjunctionHomFamily
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.CommaInitialAdjunction
public import
  SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraighteningFunctorIso
public import
  SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningInfinityReconstruction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialEquivalence

/-!
概要：共変 Hom 合成の各点の余表現から、元の全随伴を構成する。
方針：分類同型を全空間の同値に戻して comma 始対象を得て、既存の全単位の構成を使う。
規約：対象ごとの自然な Hom 表現を入力とし、随伴関手や大域単位を追加入力にしない。
使われ方：空間値余表現可能性から随伴関手定理へ接続する。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories


/-- 概要：共変表現可能な分類図式を持つ left fibration の全空間は始対象を持つ。
方針：元の coslice の分類同型を小さい unstraightening の全同値へ戻す。
規約：全空間 E の元の頂点を始対象として回収する。
使われ方：Hom 余表現による元の comma fiber の始対象の構成。 -/
lemma leftFibration_exists_initial_of_covariantRepresentation
    {E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (y : B _⦋0⦌)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity y) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p)) :
    ∃ v : E _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex v := by
  have : Quasicategory E := quasicategory_of_innerFibration p
  let q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm y)
  let h₀ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.covariantRepresentableInfinity_cosliceIso y).symm ≪≫ h
  let e₁ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityReconstruction_isPrecompositionEquivalence
    q).isQCatEquivalence.choose
  let e₂ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraighteningEquivalenceOfFunctorIso h₀
  let e₃ := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityReconstruction_isPrecompositionEquivalence
    p).isQCatEquivalence.choose
  let e := (e₁.trans e₂).trans e₃.symm
  exact ⟨e.hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone y),
    (e.isInitialVertex_iff _).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.cosliceIdentityCone_isInitialVertex y)⟩

/-- 概要：各共変 Hom 合成が元の対象で余表現可能なら、元の関手は右随伴である。
方針：元の各 comma 分類図式を余表現し、全空間の始対象から全随伴を構成する。
規約：大域単位や左随伴関手を存在入力に置かない。
使われ方：accessible な極限保存関手の左随伴の構成。 -/
lemma exists_leftAdjoint_of_covariantHom_representable
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X)
    (h : ∀ x : X _⦋0⦌, ∃ y : Y _⦋0⦌,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity y)
        ((SSet.uliftFunctor.{u + 1, u}).map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x))) :
    ∃ F : X ⟶ Y, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.exists_qcatAdjunction_of_commaFiberInitial G
  intro x
  obtain ⟨y, ⟨hy⟩⟩ := h x
  exact leftFibration_exists_initial_of_covariantRepresentation
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x) y (hy ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.CouplingsOfInfinityCategories.covariantHomCommaClassificationIso G x)

/-- 概要：元の関手の左随伴の存在は各共変 Hom 合成の元の対象による余表現可能性と同値。
方針：随伴から全自然 Hom 比較を得て、逆に comma の始対象から随伴を組み立てる。
規約：全関手の Hom 同型を使う。
使われ方：随伴関手定理の存在方向と必要方向の共通判定。 -/
lemma exists_leftAdjoint_iff_covariantHom_representable
    {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] (G : Y ⟶ X) :
    (∃ F : X ⟶ Y, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G)) ↔
      ∀ x : X _⦋0⦌, ∃ y : Y _⦋0⦌,
        Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity y)
          ((SSet.uliftFunctor.{u + 1, u}).map G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x)) := by
  constructor
  · rintro ⟨F, ⟨a⟩⟩ x
    exact ⟨F.app (Opposite.op ⦋0⦌) x, ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.CouplingsOfInfinityCategories.adjunctionCovariantHomIso a x⟩⟩
  · exact exists_leftAdjoint_of_covariantHom_representable G

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
