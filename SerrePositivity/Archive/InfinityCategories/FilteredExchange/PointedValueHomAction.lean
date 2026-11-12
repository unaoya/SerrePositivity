module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedValueFamilyTransport
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.FunctorSpaceCurrying
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UniverseInternalHom

/-!
概要：全 Kan Hom 上で、元の値による評価と同じ区間の輸送を比較する。
方針：動く点・動く射の比較を curry し、両端を元の標準作用へ厳密に同定する。
規約：全 Hom パラメータと選択済み値比較を保持。使われ方：元の精密化辺の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable (K L : KanObject.{u})
local notation "A" => vertexFiber pointedSpaceProjection (spaceInfinityVertex K)

/-- 元の全 Kan Hom を、既存の始点値比較を前合成した関手の族へ写す。 -/
def pointedValueHomEvaluation :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L) ⟶
      (ihom A).obj ((SSet.uliftFunctor.{u + 1, u}).obj L.obj) :=
  uliftInternalHomComparison K.obj L.obj ≫
    (pre (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom).app
      ((SSet.uliftFunctor.{u + 1, u}).obj L.obj)

/-- 元の右 Hom の同じ区間族を輸送し、既存の終点値比較で読む関手の族。 -/
def pointedValueHomTransport :
    (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L) ⟶
      (ihom A).obj ((SSet.uliftFunctor.{u + 1, u}).obj L.obj) :=
  coherentKanRightHomInterval K L ≫
    parametrizedFiberTransport pointedSpaceProjection (spaceInfinityVertex K)
      (spaceInfinityVertex L) ≫
    (ihom A).map (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom

/-- 元の動く点と射の評価を curry すると、標準の Hom 作用そのもの。 -/
lemma pointedValueHomEvaluation_curry :
    curry (pointedRightFamilyEvaluation
      (fst A ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)) ≫
        (pointedSpaceFiberValueEquivalence (spaceInfinityVertex K)).hom)
      (snd A ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)))) =
        pointedValueHomEvaluation K L := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro f
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 同じ対角輸送の値を curry すると、同じ普遍区間輸送の作用そのもの。 -/
lemma pointedValueHomTransport_curry :
    curry (diagonalFiberTransport pointedSpaceProjection
      (fst A ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)))
      (snd A ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)) ≫
        coherentKanRightHomInterval K L) ≫
      (pointedSpaceFiberValueEquivalence (spaceInfinityVertex L)).hom) =
        pointedValueHomTransport K L := by
  have h : diagonalFiberTransport pointedSpaceProjection
      (fst A ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)))
      (snd A ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)) ≫
        coherentKanRightHomInterval K L) = (A ◁ coherentKanRightHomInterval K L) ≫
      (parametrizedFiberTransportFamily pointedSpaceProjection (spaceInfinityVertex K)
        (spaceInfinityVertex L)).endpoint := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro p
    rfl
  rw [h, curry_natural_right, curry_natural_left]
  rfl

/-- 全 Kan Hom 上の指定比較。二つの作用を別々の代表で置き換えない。 -/
def pointedValueHomActionIso :
    FunctorIso (pointedValueHomEvaluation K L) (pointedValueHomTransport K L) :=
  functorIsoOfEq ((pointedValueFamilyTransportIso
    (fst A ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)))
    (snd A ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)))).curry)
    (pointedValueHomEvaluation_curry K L) (pointedValueHomTransport_curry K L)

end SerrePositivity.InfinityCategories.F2
