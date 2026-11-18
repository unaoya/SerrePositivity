module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaPairNaturality
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexTensorHom

/-!
# 同じ正規化標準単体の Hom と Γ の全自然比較

DAG XIII §2.2 の Ω 比較への前段。標準単体での既存の実随伴同値を
全複体について自然な関手同型へ束ねる。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom
variable (A : Type u) [CommRing A]

/-- 元の正規化標準単体を源とする Hom の全関手。 -/
def gammaStandardHom : Complex A ⥤ SSet.{u} :=
  cosimplicialHom (SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A)

/-- 各複体における、同じ標準単体 Hom の Γ との同型。 -/
def gammaStandardHomIso (M : Complex A) :
    (gammaStandardHom A).obj M ≅ (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).obj M :=
  NatIso.ofComponents (fun n => Equiv.toIso (_root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv A M n.unop)) (by
    intro n m θ
    apply ConcreteCategory.hom_ext
    intro f
    exact _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_naturality A M θ.unop f)

/-- 比較は全複体・全射に自然で、元の Γ の射への作用を保持する。 -/
def gammaStandardHomFunctorIso : gammaStandardHom A ≅ _root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A :=
  NatIso.ofComponents (gammaStandardHomIso A) (by
    intro M N f
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro g
    exact _root_.SerrePositivity.ComplexLimits.normalizedSimplexHomEquiv_postcomp A n.unop g f)

end SerrePositivity.EInfinity.PowerOperation
