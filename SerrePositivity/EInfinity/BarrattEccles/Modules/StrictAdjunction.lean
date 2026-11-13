module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.StrictModules
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelAdjunction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKernelGraphComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.UnitTransport

/-!
# 厳密 BE 射の拡大に対する実右随伴

概要：HA §4.2.3 の拡大の右随伴を、同じ dg graph の普遍余単位から構成する。
方針：一般 kernel の実随伴を、同じ拡大関手への graph 比較で移す。
規約：解像度付き dg 制限との全関手比較は別であり、定義上の一致は主張しない。
使われ方：BE 加群族の restriction の随伴と指定単位・余単位。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {A : Type u} [CommRing A]

/-- 概要：同じ拡大に対する実右随伴（HA §4.2.3）。
方針：指定 dg 代数射の graph に一般 kernel の右随伴構成を適用する。
規約：出力の射影性を仮定しない。使われ方：解像度付き制限との比較。 -/
def strictModuleAdjointRestrict {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    strictModuleInfinity A Y ⟶ strictModuleInfinity A X :=
  dgKernelRightAdjointCandidate A _ _
    (functorGraph A _ _ (dgAlgebraMap A ((assocForget A).map f)))

/-- 概要：同じ厳密射の拡大と実右随伴の native 随伴（HA §4.2.3）。
方針：graph の実随伴を全関手同型に沿って移し、両三角式を保つ。
規約：通常のホモトピー圏上だけの随伴ではない。
使われ方：指定された全単位・余単位と restriction の接続。 -/
def strictModuleGraphAdjunction {X Y : (operad A).Algebra} (f : X ⟶ Y) :
    QCatAdjunction (strictModuleExtend f) (strictModuleAdjointRestrict f) :=
  qcatAdjunctionChangeLeft
    (dgKernelAdjunction A _ _
      (functorGraph A _ _ (dgAlgebraMap A ((assocForget A).map f))))
    (dgKernelDerivedInfinity_graphIso A _ _ (dgAlgebraMap A ((assocForget A).map f)))

end SerrePositivity.EInfinity.BarrattEccles
