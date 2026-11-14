module
public import SerrePositivity.EInfinity.Modules.SimplexAugmentation
public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeAugmentationCompatibility

/-!
# 同じ元の全加群 cone 単体の厳密な augmentation

概要：同じ実 cone 単体に全次数で検証した元の閉射を付ける。
方針：元の各対象の augmentation と同じ全合成則を代入する。
規約：HA Construction 1.3.1.6・1.3.1.13、元の全列と単体を保持する。
使われ方：M10 の同じ全二重 cone の入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：同じ元の全 cone 単体と厳密に両立する同じ augmentation。
方針：元の実閉射と全合成則をそのまま束ねる。
規約：HA 1.3.1.6、同じ端点。使われ方：同じ全二重 cone。 -/
def strictRawModuleTensorConeSimplexAugmentation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    ModuleSimplexAugmentation A (dgAlgebraCategory A ((assocForget A).obj X))
      (strictRawModuleTensorConeSimplex A X P Q c) ((strictRawModuleProbeFunctor A X).obj P) where
  app := strictRawModuleTensorConeAugmentationAt A X P Q c
  hom_naturality := strictRawModuleTensorConeAugmentationAt_compose A X P Q c

/-- 概要：同じ実 augmentation の各成分は元の加群擬同型。
方針：同じ各成分の検証済みの式を取る。
規約：HA §1.3.4、同じ閉射。使われ方：同じ導来源への後合成。 -/
lemma strictRawModuleTensorConeSimplexAugmentation_app_weak {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) (i : Fin (n + 2)) :
    moduleQuasiIso A (dgAlgebraCategory A ((assocForget A).obj X))
      ((strictRawModuleTensorConeSimplexAugmentation A X P Q c).app i) :=
  strictRawModuleTensorConeAugmentationAt_quasiIso A X P Q c i

end SerrePositivity.EInfinity.BarrattEccles
