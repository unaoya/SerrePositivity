module

public import SerrePositivity.InfinityCategories.F1.RelativeSectionBaseChangeComparison
public import SerrePositivity.InfinityCategories.F1.TransportSimplexFirstVertexNaturality
public import SerrePositivity.InfinityCategories.F1.RelativeSectionJointComparison
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipAdjunction

/-!
概要：任意の底変換に対する全単体の共同切断評価の自然性。
方針：標準単体の定義域の比較と切断の豊穣的な底変換を共同実現する。
規約：全 left fibrations と全高次パラメーターを一つの関手同型で扱う。
使われ方：実際の straightening の任意の底変換との両立。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 関手の族の同型を二変数交換して同じ全パラメーターで比較する。 -/
def FunctorIso.transpose {A I X : SSet.{u}} {F G : A ⟶ (ihom I).obj X}
    (e : FunctorIso F G) :
    FunctorIso (transposeFunctorFamily F) (transposeFunctorFamily G) :=
  VertexIso.map e (internalHomSwapIso A I X).hom

/-- 族の始域の前合成は転置後に内部 Hom の制限になる。 -/
lemma transposeFunctorFamily_comp {A A' I X : SSet.{u}}
    (i : A' ⟶ A) (F : A ⟶ (ihom I).obj X) :
    transposeFunctorFamily (i ≫ F) = transposeFunctorFamily F ≫ (pre i).app X :=
  internalHomFlipHomEquiv_pre i F

/-- 全添字と全対象で共同実現した切断の底変換同型。 -/
def relativeSectionDiagramInfinityBaseChangeIso {B D : SSet.{u}}
    {J : Type u} [Category.{u} J] (k : D ⟶ B) (A : Jᵒᵖ ⥤ Over D) :
    FunctorIso
      (relativeSectionDiagramInfinity A ≫ (pre (leftFibrationInfinityBaseChange k)).app
        SpaceInfinity.{u})
      (relativeSectionDiagramInfinity (A ⋙ Over.map k)) := by
  have e := (relativeSectionBaseChangeRealizationIso k A).transpose
  rw [transposeFunctorFamily_comp] at e
  exact e

/-- 全単体の定義域は底の射での合成と厳密に両立する。 -/
lemma transportSimplexDomainFunctor_baseChange {B D : SSet.{u}} (k : D ⟶ B) :
    (transportSimplexFunctor k).op ⋙ transportSimplexDomainFunctor B =
      transportSimplexDomainFunctor D ⋙ Over.map k := by
  refine CategoryTheory.Functor.ext (fun s ↦ ?_) ?_
  · change Over.mk (SSet.yonedaEquiv.symm (k.app _ s.unop.objDown.val)) =
      Over.mk (SSet.yonedaEquiv.symm s.unop.objDown.val ≫ k)
    exact congrArg Over.mk (SSet.yonedaEquiv_symm_comp _ k).symm
  · intro s t f
    apply Over.OverMorphism.ext
    simp
    rfl

/-- 全単体の共同切断評価は任意の底変換と関手同型で両立する。 -/
def transportSimplexSectionInfinity_baseChangeIso {B D : SSet.{u}} (k : D ⟶ B) :
    FunctorIso
      (transportSimplexSectionInfinity D ≫
        (pre (leftFibrationInfinityBaseChange k)).app SpaceInfinity.{u})
      ((SSet.uliftFunctor.{u + 1, u}).map (nerveMap (transportSimplexFunctor k)) ≫
        transportSimplexSectionInfinity B) := by
  rw [transportSimplexSectionInfinity_reindex, transportSimplexDomainFunctor_baseChange]
  exact relativeSectionDiagramInfinityBaseChangeIso k (transportSimplexDomainFunctor D)

end SerrePositivity.InfinityCategories
