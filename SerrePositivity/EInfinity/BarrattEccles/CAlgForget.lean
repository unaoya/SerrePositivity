module

public import SerrePositivity.EInfinity.BarrattEccles.CAlg
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.NerveMap

/-!
# CAlg_R から全複体の単体的局所化への忘却

概要：任意の可換環上の CAlg_R の忘却を全複体の局所化の nerve へ構成する。
方針：元の忘却相対関手の Hom を同じ宇宙へ上げ、一般の nerve の係数射へ送る。
規約：底の複体に cofibrancy を仮定しない。既存 D(R) との比較は後続。
使われ方：E2b の忘却 ∞ 関手とその D(R) への比較の入力。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory
open SerrePositivity.DifferentialGraded
open _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open scoped Simplicial

variable (A : Type u) [CommRing A]

/-- 概要：全複体と擬同型を同じ宇宙の DK 相対圏に束ねる（Dwyer–Kan）。
方針：Hom のみを ULift し、元の擬同型類を引き戻す。
規約：全複体を使い、cofibrancy の条件を付けない。
使われ方：CAlg_R の忘却の局所化先。 -/
def complexRelativeCategory : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u + 1} where
  category := Cat.of (ULiftHom.{u + 1} (Complex A))
  weakEquivalences := (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).inverseImage
    (ULiftHom.down.{u, u + 1, u + 1} (C := Complex A))
  isMultiplicative := inferInstance

/-- 概要：元の忘却相対関手を同じ宇宙の全複体へ送る（BM 命題 4.1）。
方針：同じ忘却の Hom のみを ULift し、元の擬同型保存を使う。
規約：元の複体・射・弱同値を保持する。
使われ方：局所化の nerve の間の忘却射。 -/
def cAlgForgetRelative :
    cofibrantAlgebraRelativeCategory A ⟶ complexRelativeCategory A where
  functor := cofibrantAlgebraDKForget A ⋙ (ULiftHom.up.{u, u + 1, u + 1} (C := Complex A))
  map _ _ f hf := (cofibrantAlgebraDKForgetRelative A).map f hf

/-- 概要：全複体の具体的な単体的局所化の nerve（Dwyer–Kan、HTT §1.1.5）。
方針：同じ自由局所化・Ex∞・coherent nerve を全複体へ適用する。
規約：既存の dg nerve の D(R) との同値は後続で証明する。
使われ方：CAlg_R の忘却射の具体的な終域。 -/
def complexLocalizationNerve : SSet.{u + 1} := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve (complexRelativeCategory A)

/-- 概要：全複体の同じ局所化の nerve は quasicategory（HTT 1.1.5.10）。
方針：一般の局所化の Kan Hom の定理を代入する。
規約：複体や単体集合のモデル構造の入力仮定は不要。
使われ方：忘却の終域の ∞ 圏構造。 -/
instance complexLocalizationNerve_quasicategory :
    SSet.Quasicategory (complexLocalizationNerve A) := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerve_quasicategory _

/-- 概要：CAlg_R から全複体の具体的局所化への忘却射（Dwyer–Kan）。
方針：同じ元の忘却相対関手を一般の nerve 係数射へ送る。
規約：底の cofibrancy を要求しない。既存 D(R) への比較は後続。
使われ方：E2b の忘却 ∞ 関手の具体的な第一段階。 -/
def cAlgForgetLocalization : CAlg_R A ⟶ complexLocalizationNerve A :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap (cAlgForgetRelative A)

/-- 概要：同じ忘却射の頂点は元の置換の底の複体（Dwyer–Kan）。
方針：一般の nerve の頂点自然性に同じ置換を代入する。
規約：元の関手的 cofibrant 置換を保持する。
使われ方：既存 D(R) の対象との比較。 -/
lemma cAlgForgetLocalization_vertex (X : (operad A).Algebra) :
    (cAlgForgetLocalization A).app (Opposite.op ⦋0⦌) (cAlgVertex A X) =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveVertexEquiv (complexRelativeCategory A)
        ((cofibrantAlgebraDKForget A).obj ((cofibrantAlgebraDKReplacement A).obj X)) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.localizationNerveMap_vertex (cAlgForgetRelative A) ((cofibrantAlgebraDKReplacement A).obj X)

end SerrePositivity.EInfinity.BarrattEccles
