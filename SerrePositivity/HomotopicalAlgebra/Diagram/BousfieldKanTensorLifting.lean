module

public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanWeightCofibrancy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodynePullbackHom
public import SerrePositivity.CategoryTheory.Adjunction.Comparison

/-!
概要：BK重みとanodyneなパラメータのtensorは係数fibrationに対して持ち上がる。
方針：成分ごとの相対内部Homへ二変数随伴で移し、BK重みの既存のLLPを使う。
使われ方：HTT 4.2.4.4、RR02(a)の実現随伴の相対horn条件。
規約：パラメータを左因子に置き、SSetのモデル構造は仮定しない。
-/

@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen
open SerrePositivity.PointwiseAdjunction
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.DiagramModel
variable (K : Type u) [SmallCategory K]

/-- 二変数随伴でBK重みの射影的LLPから移した、実際のtensor射の持ち上げ。 -/
lemma bousfieldKanTensor_hasLiftingProperty {A B : SSet.{u}}
    (i : A ⟶ B) (hi : SSet.anodyneExtensions i)
    {F G : K ⥤ SSet.{u}} (p : F ⟶ G) [∀ k, Fibration (p.app k)] :
    HasLiftingProperty
      (((pointwise K (curriedTensor SSet.{u})).map i).app (bousfieldKanWeight K)) p := by
  have (X : SSet.{u}) : ((pointwise K (curriedTensor SSet.{u})).obj X).IsLeftAdjoint :=
    ((PointwiseAdjunction.adjunction K internalHomAdjunction₂).adj X).isLeftAdjoint
  let sq := Functor.PushoutObjObj.ofIsInitialRight
    (pointwise K (curriedTensor SSet.{u})) i
    (initial.to (bousfieldKanWeight K)) initialIsInitial
  let sq' := Functor.PullbackObjObj.ofHasPullback (pointwise K internalHom) i p
  change HasLiftingProperty sq.ι p
  rw [(PointwiseAdjunction.adjunction K internalHomAdjunction₂).hasLiftingProperty_iff sq sq']
  apply bousfieldKanWeight_projective_llp K sq'.π
  intro k
  exact (SimplicialModel.anodyne_pullbackHom_trivialKanFibration i hi (p.app k)
    (evaluatePullbackObjObj K internalHom i p sq' k)).mem

end SerrePositivity.DiagramModel
