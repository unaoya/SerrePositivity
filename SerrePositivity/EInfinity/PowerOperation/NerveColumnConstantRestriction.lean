module

public import SerrePositivity.EInfinity.FrameHom.NerveColumnRoofNaturality
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.Reindexing.ConstantRestrictionArrow

/-!
# 同じ全関手同型の通常定値列での制限

DAG XIII §2.2 の指定屋根の照合の補助。全 sourceIso の制限を、同じ頂点成分の
全定値族へ戻す。［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory SSet MonoidalClosed
open SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries
open FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open scoped Simplicial
variable (I C : Type u) [Category.{u} I] [Category.{u} C]

lemma nativeNerveMap_const (x : C) :
    nerveMap ((Functor.const I).obj x) = SSet.const (ComposableArrows.mk₀ x) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro σ
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

lemma nerveColumnConstantRestriction_arrow {D : SSet.{u}} {F G : nerve C ⟶ D}
    (e : FunctorIso F G) (x : C) :
    Arrow.mk (e.precomp (nerveMap ((Functor.const I).obj x))).hom =
      Arrow.mk (constantFunctorHomMap (nerve I)
        (functorIsoEvaluate e (ComposableArrows.mk₀ x)).hom) := by
  have h := congrArg (fun q : nerve I ⟶ nerve C =>
    Arrow.mk ((hoFunctor.map ((pre q).app D)).toFunctor.map e.hom)) (nativeNerveMap_const I C x)
  exact h.trans (constantRestriction_arrow (nerve I) e.hom (ComposableArrows.mk₀ x))

end SerrePositivity.EInfinity.PowerOperation
