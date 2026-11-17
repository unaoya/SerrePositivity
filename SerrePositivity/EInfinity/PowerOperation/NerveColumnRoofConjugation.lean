module

public import SerrePositivity.EInfinity.PowerOperation.NerveColumnConstantRestriction
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoPrecompositionCoherence
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefixColumnRoof
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CoherentPinchedTransport

/-!
# 同じ sourceIso の両端成分で全屋根族を共役する

DAG XIII §2.2 の指定比較の照合の補助。全関手の屋根の自然性と定値制限の
全 Arrow の等式を接続する。［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet
open _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors
open AdjointFunctorsBetweenInfinityCategories (intervalFamilyHom)
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open IsomorphismsAndIsofibrations (IsInvertibleEdge)
open scoped Simplicial
variable {I C : Type u} [Category.{u} I] [Category.{u} C]
  {D : SSet.{u}} [Quasicategory D] {F G : nerve C ⟶ D} (e : FunctorIso F G)
  (V : I ⥤ C) {X Y : C} (p : V ⟶ (Functor.const I).obj X)
  (hpF : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map F).toTruncated)
  (hpG : ∀ i, IsInvertibleEdge ((nerve.edgeMk (p.app i)).map G).toTruncated)
  (s : V ⟶ (Functor.const I).obj Y)

lemma nerveColumnRoofConjugation_arrow
    (f : nerve I ⟶ MorphismSpaces.Basic.pinchedHom
      (F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ X))
      (F.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ Y)))
    (hf : Arrow.mk (intervalFamilyHom (f ≫ MorphismSpaces.pinchedHomToIntervalMappingSpace _ _)) =
      Arrow.mk ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso F V p hpF).inv ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom F s)) :
    Arrow.mk (constantFunctorHomMap (nerve I)
        (functorIsoEvaluate e (ComposableArrows.mk₀ X)).inv ≫
      intervalFamilyHom (f ≫ MorphismSpaces.pinchedHomToIntervalMappingSpace _ _) ≫
      constantFunctorHomMap (nerve I) (functorIsoEvaluate e (ComposableArrows.mk₀ Y)).hom) =
      Arrow.mk ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso G V p hpG).inv ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom G s) := by
  have hx := nerveColumnConstantRestriction_arrow I C e.symm X
  have hy := nerveColumnConstantRestriction_arrow I C e Y
  have h₁ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.comp_arrow_eq _ _ _ _ hx.symm hf
  have h₂ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.RoofPrefix.comp_arrow_eq _ _ _ _ h₁ hy.symm
  have hn : (e.precomp (nerveMap ((Functor.const I).obj X))).inv ≫
      ((_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso F V p hpF).inv ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom F s) ≫
      (e.precomp (nerveMap ((Functor.const I).obj Y))).hom =
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso G V p hpG).inv ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom G s := by
    apply (cancel_epi (e.precomp (nerveMap ((Functor.const I).obj X))).hom).mp
    simp only [Iso.hom_inv_id_assoc]
    simpa only [Category.assoc] using (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.roof_naturality e V p hpF hpG s).symm
  have hn' : ((FunctorIso.precomp e.symm (nerveMap ((Functor.const I).obj X))).hom ≫
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso F V p hpF).inv ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom F s) ≫
      (e.precomp (nerveMap ((Functor.const I).obj Y))).hom =
      (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.augmentationIso G V p hpG).inv ≫ _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.NerveColumn.hom G s := by
    simpa only [Category.assoc, FunctorIso.precomp_symm, Iso.symm_hom] using hn
  have h₃ := h₂.trans (congrArg Arrow.mk hn')
  simpa only [Category.assoc, functorIsoEvaluate, Iso.symm_hom] using h₃

end SerrePositivity.EInfinity.PowerOperation
