module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInfinityVertices
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovInfinityCone
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.RepresentableLimitCharacterization
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HomCovariantComparison
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.OppositeFunctorIso
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.UniverseEdgeTransport

/-!
概要：元の局所化 Postnikov 錐の極限性は、実 cell 像を源とする表現可能試験で検出する。
方針：全局所化頂点の cell 像表示と、元の全共同 Hom の第一変数自然性を使う。
規約：試験錐の極限性はまだ証明せず、導来写像模型との比較を追加入力で代替しない。
使われ方：実 cell 写像模型との全自然比較を適用する正確な極限判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n)

lemma postnikovInfinityCone_isLimit_iff_cellTests :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (postnikovInfinityCone R B n hn) ↔
      ∀ A : Mon (Complex R), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity
          (quasiIsoInfinityVertex R (cellResolution R A)))
          (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u + 1, u + 2} (postnikovInfinityCone R B n hn))) := by
  constructor
  · intro hc A
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.covariantRepresentableInfinity_isLimit _ hc _
  · intro hc
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.isLimitCone_of_covariantRepresentableInfinity
    intro x
    obtain ⟨A, ⟨e⟩⟩ := exists_cellResolutionInfinityVertexIso R x
    let eu : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso
        (X := SSet.uliftFunctor.{u + 2, u + 1}.obj (quasiIsoInfinity R).op)
        (ULift.up (SSet.opObjEquiv.symm (quasiIsoInfinityVertex R (cellResolution R A))))
        (ULift.up (SSet.opObjEquiv.symm x)) :=
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.upFunctor.{u + 1, u + 2} (quasiIsoInfinity R).op).mapIso (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.VertexIso.op e)
    have eh : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant
        (quasiIsoInfinityVertex R (cellResolution R A))) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.homInfinityCovariant x) := by
      have he := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map eu (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap (quasiIsoInfinity R))
      simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coyonedaInfinityMap_vertex] using he
    let ec : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity
        (quasiIsoInfinityVertex R (cellResolution R A))) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.covariantRepresentableInfinity x) :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homInfinityCovariant_covariantIso _).symm ≪≫ eh ≪≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.homInfinityCovariant_covariantIso _
    exact (hc A).of_functorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp ec
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCone.ulift.{u + 1, u + 2} (postnikovInfinityCone R B n hn)).val)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
