module

public import SerrePositivity.EInfinity.BarrattEccles.MappingResolutionAsphericity
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ResolutionCofinality

/-!
# 元の E 代数の Map^h の分解の実際の余終性

概要：任意の可換環上の同じ写像空間の分解の nerve の余終性を与える。
方針：同じ転送モデルと同じ関手的分解を一般の Quillen A の結論へ局所代入する。
規約：元の代数の cofibrancy や単体集合モデルを入力しない。
使われ方：三本矢への共通比較の右射の具体的な分解側の余終性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open SerrePositivity.Reedy
open SerrePositivity.InfinityCategories

variable (A : Type u) [CommRing A]

/-- 概要：元の写像空間の分解の同じ宇宙の小圏への比較（Low 命題 3.6）。
方針：同じ分解の前後で対象と射の up・down を行う。
規約：元の分解と全作用素を保持する。
使われ方：実際の分解側の余終性の比較射。 -/
def mappingSmallResolutionOverFunctor (X : (operad A).Algebra) :
    AsSmall.{u + 1} SimplexCategory ⥤ AsSmall.{u + 1} (algebraTrivialFibrationOver A X) := by
  let := modelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.smallResolutionOverFunctor
    ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X)

/-- 概要：実際の写像空間の分解の nerve は left cofinal（Low 命題 3.6）。
方針：全 comma の可縮性による一般の Quillen A の結論へ同じ分解を代入する。
規約：任意の可換環・任意の元の代数を扱う。
使われ方：三本矢への右射の具体的な分解側のホモトピー余終性。 -/
lemma mappingSmallResolutionOverFunctor_isLeftCofinal (X : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap (mappingSmallResolutionOverFunctor A X)) := by
  let := modelCategory A
  exact _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.smallResolutionOverFunctor_isLeftCofinal
    ((cosimplicialResolutionFamily (mappingCofibrantFactorization A)).atObject X)

/-- 概要：元の Map^h の分解の同じ nerve は弱ホモトピー同値（Low 命題 3.6）。
方針：同じ具体的な left cofinality を全 Kan 標的で検査する。
規約：同じ比較射を保持し、nerve の Kan 性を要求しない。
使われ方：元の分解の比較のホモトピー型。 -/
lemma mappingSmallResolutionOverFunctor_isWeakHomotopyEquivalence (X : (operad A).Algebra) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (mappingSmallResolutionOverFunctor A X)) :=
  (mappingSmallResolutionOverFunctor_isLeftCofinal A X).isWeakHomotopyEquivalence

end SerrePositivity.EInfinity.BarrattEccles
