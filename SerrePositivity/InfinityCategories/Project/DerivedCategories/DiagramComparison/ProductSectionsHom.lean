module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.FreeChainsAdjunction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StandardSimplexParameter
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.AdjunctionHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseJoinSimplexShapes
public import SerrePositivity.HomotopicalAlgebra.Simplicial.StandardSimplexCosimplicialHom

/-!
概要：積重みの自由鎖からの全単体 Hom を、元の重み付き切断空間に同定する。
方針：自由鎖と重み付き切断の随伴を合成し、同じ標準単体の Yoneda 同型を使う。
規約：元の重み・図式・単体作用素を保ち、空間の同値性を追加仮定しない。
使われ方：HA 1.2.4、G10 の積重み側の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison

/-- 持ち上げた小さい標準単体と同じ宇宙の標準単体の全自然同型。 -/
def liftedStandardSimplexIso :
    SSet.stdSimplex.{0} ⋙ SSet.uliftFunctor.{u,0} ≅ SSet.stdSimplex.{u} :=
  NatIso.ofComponents (fun n => uliftStdSimplexIso.{0,u} n.len) (by
    intro n m f
    exact uliftStdSimplexIso_hom_map f)

/-- 同じ持ち上げ標準単体からの Hom は元の単体集合。 -/
def liftedStandardSimplexHomIso (Z : SSet.{u}) :
    (cosimplicialHom (SSet.stdSimplex.{0} ⋙ SSet.uliftFunctor.{u,0})).obj Z ≅ Z :=
  ((cosimplicialHomBifunctor.mapIso liftedStandardSimplexIso.op).app Z).symm ≪≫
    SerrePositivity.HomotopyFunctionComplex.QuillenStandardFrame.homIso.app Z

variable (A : Type u) [CommRing A] {J : Type u} [SmallCategory J]
variable (X : J ⥤ SSet.{u}) (Q : J ⥤ CochainComplex (ModuleCat A) ℤ)

/-- 積重みの自由鎖からの Hom と、元の実 Γ 図式の重み付き切断の全単体同型。 -/
def freeProductSectionsHomIso :
    (cosimplicialHom (freeProductFrame A X (liftedStandardSimplexParameter J))).obj Q ≅
      weightedSections X (Q ⋙ truncatedDoldKanFunctor A) :=
  ((adjunctionHomIsoSameUniverse
    ((weightedSectionsAdjunction X).comp (freeNegativeChainsDiagramAdjunction A J))
      (SSet.stdSimplex.{0} ⋙ SSet.uliftFunctor.{u,0})).app Q) ≪≫
    liftedStandardSimplexHomIso _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
