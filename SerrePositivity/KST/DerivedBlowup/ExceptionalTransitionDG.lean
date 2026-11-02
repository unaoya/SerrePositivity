module

public import SerrePositivity.KST.DerivedBlowup.ExceptionalTransitionChart
public import SerrePositivity.KST.DerivedBlowup.ChartDGFunctors
public import SerrePositivity.KST.DerivedBlowup.ExteriorCochainMapTransport
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
概要：KST v4 Lemma 3.6（pp.11–14）の例外因子の重なりを Koszul dg 関手にする。
方針：共通の全 a_j 表示を介する基底同型を外積に延長し、関手性で cocycle を保つ。
規約：同一重なり環上の表示。係数移送を含む大域図式との比較は別に残す。
使われ方：例外因子の局所 dg 比較の重なりでの整合性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable {B : Type (max u v)} [CommRing B] {I : Type v} [DecidableEq I]

/-- 概要：例外因子の重なりの指定 dg 遷移。
方針：可逆生成元変換と微分適合性を既存の外積 dg 関手へ渡す。
規約：KST Lemma 3.6、k から i へ向く。使われ方：局所図式の遷移。 -/
def exceptionalTransitionDGFunctor (a x y : I → B) (i k : I) :
    DGFunctor B
      (ExteriorKoszulObject (Finsupp.linearCombination B (exceptionalRelationValue a y k)))
      (ExteriorKoszulObject (Finsupp.linearCombination B (exceptionalRelationValue a x i))) :=
  exteriorKoszulDGFunctor (exceptionalTransitionEquiv i k x y).toLinearMap
    (Finsupp.linearCombination B (exceptionalRelationValue a y k))
    (Finsupp.linearCombination B (exceptionalRelationValue a x i))
    (exceptionalTransitionEquiv_differential a x y i k)

/-- 概要：例外因子の指定 dg 遷移の全 Hom 写像は同型。
方針：生成元の線形同型から指定 cochain 同型を作る。
規約：KST Lemma 3.6。使われ方：重なりでの dg 可逆性。 -/
theorem exceptionalTransitionDGFunctor_map_isIso (a x y : I → B) (i k : I) (M N) :
    IsIso ((exceptionalTransitionDGFunctor a x y i k).map M N) := by
  change IsIso (exteriorKoszulCochainIso (exceptionalTransitionEquiv i k x y)
    (Finsupp.linearCombination B (exceptionalRelationValue a y k))
    (Finsupp.linearCombination B (exceptionalRelationValue a x i))
    (exceptionalTransitionEquiv_differential a x y i k)).hom
  infer_instance

/-- 概要：例外因子の dg 遷移は cocycle を満たす。
方針：生成元変換の cocycle を外積 cochain 写像の合成則で移す。
規約：KST Lemma 3.6、同一係数環へ移した三つの表示。
使われ方：全有限重なり dg 図式の合成整合性。 -/
theorem exceptionalTransitionDGFunctor_cocycle (a x y z : I → B) (i k l : I) :
    (exceptionalTransitionDGFunctor a y z k l).comp (exceptionalTransitionDGFunctor a x y i k) =
      exceptionalTransitionDGFunctor a x z i l := by
  refine EnrichedFunctor.ext (Complex B) (fun _ => rfl) ?_
  intro M N
  simp only [eqToHom_refl, Category.comp_id]
  exact exteriorKoszulCochainMap_comp_eq
    (exceptionalTransitionEquiv k l y z).toLinearMap
    (exceptionalTransitionEquiv i k x y).toLinearMap
    (exceptionalTransitionEquiv i l x z).toLinearMap _ _ _
    (exceptionalTransitionEquiv_differential a y z k l)
    (exceptionalTransitionEquiv_differential a x y i k)
    (exceptionalTransitionEquiv_differential a x z i l)
    (congrArg LinearEquiv.toLinearMap (exceptionalTransitionEquiv_cocycle i k l x y z))

/-- 概要：同一表示の例外因子の dg 遷移は恒等。
方針：生成元の恒等律と外積 dg 関手の恒等保存を使う。
規約：KST Lemma 3.6。使われ方：局所 dg 図式の単位条件。 -/
theorem exceptionalTransitionDGFunctor_id (a x : I → B) (i : I) :
    exceptionalTransitionDGFunctor a x x i i =
      DGFunctor.id (ExteriorKoszulObject
        (Finsupp.linearCombination B (exceptionalRelationValue a x i))) := by
  unfold exceptionalTransitionDGFunctor
  have h : (exceptionalTransitionEquiv i i x x).toLinearMap = LinearMap.id :=
    congrArg LinearEquiv.toLinearMap (exceptionalTransitionEquiv_id i x)
  simp only [h]
  exact exteriorKoszulDGFunctor_id _ _

/-- 概要：例外因子の dg 遷移と共通 Koszul 表示への比較は可換。
方針：生成元での比較式を外積 cochain 写像の合成則へ適用する。
規約：KST Lemma 3.6。使われ方：Ko(A;a)[S] 表示の局所比較の整合性。 -/
theorem exceptionalTransitionDGFunctor_comparison (a x y : I → B) (i k : I) :
    (exceptionalTransitionDGFunctor a x y i k).comp (exceptionalExteriorDGFunctor a x i) =
      exceptionalExteriorDGFunctor a y k := by
  refine EnrichedFunctor.ext (Complex B) (fun _ => rfl) ?_
  intro M N
  simp only [eqToHom_refl, Category.comp_id]
  apply exteriorKoszulCochainMap_comp_eq _ _ _ _ _ _
    (exceptionalTransitionEquiv_differential a x y i k)
    (exceptionalGeneratorMap_differential a x i)
    (exceptionalGeneratorMap_differential a y k)
  apply LinearMap.ext
  exact exceptionalTransitionEquiv_comparison i k x y

end SerrePositivity.KST.DerivedBlowup
