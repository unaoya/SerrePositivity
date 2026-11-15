module
public import SerrePositivity.EInfinity.Modules.RightConeSimplex
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeSimplexAugmentation

/-!
# 同じ元の augmentation による全加群二重 cone 単体

概要：元の全 cone 単体に、同じ probe を終端として追加する。
方針：全 HA 方程式を満たす右 cone に同じ実 augmentation を代入する。
規約：HA Construction 1.3.1.6・1.3.1.13、同じ全列と全成分を保持する。
使われ方：M10 の同じ大域的な三角形の実二重 cone。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：同じ元の全 cone と augmentation の実二重 cone。
方針：同じ検証済みの全 augmentation を右 cone へ代入する。
規約：HA 1.3.1.6、全 HA 方程式。使われ方：全三角形の元の実単体。 -/
def strictRawModuleTensorDoubleConeSimplex {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    Simplex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X))) (n + 2) :=
  moduleRightConeSimplex A (dgAlgebraCategory A ((assocForget A).obj X))
    (strictRawModuleTensorConeSimplexAugmentation A X P Q c)

/-- 概要：同じ二重 cone の前面は元の cone 単体。
方針：同じ右 cone の検証済みの前面の式を使う。
規約：HA 1.3.1.6、同じ全成分。使われ方：元の cone の回収。 -/
lemma strictRawModuleTensorDoubleConeSimplex_front {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorDoubleConeSimplex A X P Q c).pullback Fin.castSuccOrderEmb.toOrderHom =
      strictRawModuleTensorConeSimplex A X P Q c :=
  moduleRightConeSimplex_front A (dgAlgebraCategory A ((assocForget A).obj X))
    (strictRawModuleTensorConeSimplexAugmentation A X P Q c)

/-- 概要：同じ二重 cone の終端は元の probe。
方針：同じ右 cone の終端の式を使う。
規約：HA 1.3.1.6、元の対象。使われ方：元の全三角形の終端。 -/
lemma strictRawModuleTensorDoubleConeSimplex_last {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (strictRawModuleTensorDoubleConeSimplex A X P Q c).obj (Fin.last (n + 2)) =
      ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P) :=
  moduleRightConeObj_last A (dgAlgebraCategory A ((assocForget A).obj X))
    (strictRawModuleTensorConeSimplex A X P Q c) ((strictRawModuleProbeFunctor A X).obj P)

end SerrePositivity.EInfinity.BarrattEccles
