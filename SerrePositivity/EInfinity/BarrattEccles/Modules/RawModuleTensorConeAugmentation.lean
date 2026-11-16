module

public import SerrePositivity.EInfinity.BarrattEccles.Modules.RawModuleTensorConeSource
public import SerrePositivity.EInfinity.Modules.TensorAugmentationIdentity

/-!
# 元の全要素列の普遍族と同じ augmentation の全成分

概要：M10 の同じ全普遍 pinched 族を元の augmentation で送る。
方針：同じ終端パラメータで元の全定値化の式を前合成する。
規約：HA 1.3.1.13、同じ零次像と元の恒等辺への較正を保持する。
使われ方：同じ全 cone と augmentation の三角形の実係数。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Opposite SSet
open SerrePositivity.DifferentialGraded SerrePositivity.EInfinity.Modules
open SerrePositivity.InfinityCategories.HA.Section7_1_1
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open scoped Simplicial
variable (A : Type u) [CommRing A] (X : (operad A).Algebra)
  (P : strictRawModuleProbeCategory A X) (Q : strictRawModuleCategory A X)

/-- 概要：同じ全普遍族の元の augmentation 像は同じ零次像の定値族。
方針：元の全 augmentation の式を同じ終端パラメータで前合成する。
規約：HA 1.3.1.13、同じ全列。使われ方：全三角形の元の projection。 -/
lemma strictRawModuleTensorElementPinchedFamily_augmentation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorElementPinchedFamily A X P Q c ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (Fin.last n)))) =
    SSet.const (moduleTensorAugmentationPinchedVertex A
      (dgAlgebraCategory A ((assocForget A).obj X)) ((strictRawModuleProbeFunctor A X).obj P)) := by
  dsimp only [strictRawModuleTensorElementPinchedFamily]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => SSet.uliftFunctor.{u + 1, u}.map (SSet.stdSimplex.map
      (strictRawModuleTensorElementTerminalParameter A X P Q c)) ≫ f)
      (moduleTensorUniversalPinchedSimplex_augmentation A
        (dgAlgebraCategory A ((assocForget A).obj X)) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementDegree A X P Q).obj (c.obj (Fin.last n))))).trans
      (SSet.comp_const _ _))

/-- 概要：同じ全単体の augmentation 像は同じ指定零単体の定数単体。
方針：同じ全族の等式を元の恒等単体で評価する。
規約：HA 1.3.1.13、同じ元の単体。使われ方：全 cochain の augmentation 成分。 -/
lemma strictRawModuleTensorElementPinchedSimplex_augmentation {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (Fin.last n))))).app
        (op ⦋n⦌) (strictRawModuleTensorElementPinchedSimplex A X P Q c) =
    (PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))).map
        (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (moduleTensorAugmentationPinchedVertex A (dgAlgebraCategory A ((assocForget A).obj X))
        ((strictRawModuleProbeFunctor A X).obj P)) := by
  have h := congrArg (fun f : SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u}) ⟶
      PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) =>
      f.app (op ⦋n⦌) (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))))
    (strictRawModuleTensorElementPinchedFamily_augmentation A X P Q c)
  exact h


/-- 概要：元の全普遍族の augmentation 像は同じ元の恒等閉辺の定値族。
方針：同じ全定値化と元の零次像の恒等辺への較正を合成する。
規約：HA 1.3.1.13、全列・全次数。使われ方：同じ全 cone の単位三角形。 -/
lemma strictRawModuleTensorElementPinchedFamily_augmentation_identity {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    strictRawModuleTensorElementPinchedFamily A X P Q c ≫
      pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
        ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (Fin.last n)))) =
    SSet.const (pinchedClosedVertex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (𝟙 ((strictRawModuleProbeFunctor A X).obj P))) := by
  exact (strictRawModuleTensorElementPinchedFamily_augmentation A X P Q c).trans
    (congrArg (fun z => SSet.const (X := SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u})) z)
      (moduleTensorAugmentationVertex_identity A (dgAlgebraCategory A ((assocForget A).obj X))
        ((strictRawModuleProbeFunctor A X).obj P)))

/-- 概要：同じ実普遍単体の augmentation 像は元の恒等辺の定数単体。
方針：同じ全族の恒等式を同じ恒等単体で評価する。
規約：HA 1.3.1.13、元の全高次。使われ方：同じ全三角形の恒等成分。 -/
lemma strictRawModuleTensorElementPinchedSimplex_augmentation_identity {n : ℕ}
    (c : ComposableArrows (strictRawModuleTensorElementIndex A X P Q) n) :
    (pinchedHomChainMap (eHomWhiskerLeft (Complex A) ((strictRawModuleProbeFunctor A X).obj P)
      ((strictRawModuleTensorElementAugmentation A X P Q).app (c.obj (Fin.last n))))).app
        (op ⦋n⦌) (strictRawModuleTensorElementPinchedSimplex A X P Q c) =
    (PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
      (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))).map
        (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
      (pinchedClosedVertex A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (𝟙 ((strictRawModuleProbeFunctor A X).obj P))) := by
  have h := congrArg (fun f : SSet.uliftFunctor.{u + 1, u}.obj (Δ[n] : SSet.{u}) ⟶
      PinchedHom.pinchedHom A (RightModule A (dgAlgebraCategory A ((assocForget A).obj X)))
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P))
        (ForgetEnrichment.to (Complex A) ((strictRawModuleProbeFunctor A X).obj P)) =>
      f.app (op ⦋n⦌) (ULift.up (SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌))))
    (strictRawModuleTensorElementPinchedFamily_augmentation_identity A X P Q c)
  exact h

end SerrePositivity.EInfinity.BarrattEccles
