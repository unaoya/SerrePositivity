module

public import SerrePositivity.KST.NonConnective.SingleRealizationZero
public import SerrePositivity.KST.NonConnective.KanReplacementZero
public import SerrePositivity.KST.SConstruction.McCarthyFiberSection

/-!
概要：S• 加法性の二つの標準零 cofiber 軸の、元の評価公式。
方針：元の正方形の角で計算し、零関手の実 Kan 置換の群作用を使う。
規約：標準軸の評価を追加仮定とせず証明する。
使われ方：中央項の加法性と swindle の消去。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction
open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective

/-- 左標準軸の subobject は恒等完全関手。 -/
lemma cofiberAxisLeft_subobject (X : StableModel.{u}) (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex X.carrier) :
    zeroCofiberStableFunctor X z false ≫ cofiberStableSubobject X = 𝟙 X :=
  Subtype.ext (zeroCofiberStableFunctor_subobject X z false)

/-- 左標準軸の quotient は同じ指定零対象への定値完全関手。 -/
lemma cofiberAxisLeft_quotient (X : StableModel.{u}) (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex X.carrier) :
    zeroCofiberStableFunctor X z false ≫ cofiberStableQuotient X = stableConstantZero X z := by
  apply Subtype.ext
  exact zeroCofiberFunctor_quotient z false

/-- 両方の標準軸の middle は恒等完全関手。 -/
lemma cofiberAxes_middle (X : StableModel.{u}) (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex X.carrier) (b : Bool) :
    zeroCofiberStableFunctor X z b ≫ cofiberStableMiddle X = 𝟙 X := by
  apply Subtype.ext
  change zeroCofiberFunctor z b ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 0) = _
  rw [← Category.assoc, zeroCofiberFunctor_ι, zeroCofiberSquare_evaluation]
  cases b <;> rfl

/-- 同じ零関手の一重境界商 Kan 模型への作用は正次数群上で零。 -/
lemma singleBoundaryKanGroup_constantZero (X : StableModel.{u}) (z : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroVertex X.carrier)
    (n : ℕ) (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup ((boundaryKanRealizationFunctor 0).obj X).right n
      ((boundaryKanRealizationFunctor 0).obj X).basepoint) :
    pointedGroupMap n ((boundaryKanRealizationFunctor 0).map (stableConstantZero X z)) a = 1 := by
  change pointedGroupMap n
    (PointedKanReplacement.map (boundaryReducedRealizationMap 0 (stableConstantZero X z))) a = _
  rw [singleBoundary_constantZero]
  exact pointedKanReplacement_zero_group _ _ n a

end SerrePositivity.KST.NonConnective
