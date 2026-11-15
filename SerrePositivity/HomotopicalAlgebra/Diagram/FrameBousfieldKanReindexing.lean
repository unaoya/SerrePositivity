module

public import SerrePositivity.HomotopicalAlgebra.Diagram.FrameWeightReindexing
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.BousfieldKanWeightPost

/-!
概要：Bousfield–Kan重みを用いるframe実現の指定添字変更射。
方針：既存のOver.postによる重み比較を作用させ、実現の添字変更射へ合成する。
規約：制限重みと元のBK重みを同一視しない。弱同値性は別の証明対象。
使われ方：HTT 4.2.4.4のRR02(a)、評価点の実現比較と指定増大射の照合。
-/

@[expose] public noncomputable section
universe w u
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.DiagramModel.FrameWeightRealization
variable {K L : Type w} [SmallCategory K] [SmallCategory L]
  {C : Type u} [Category.{w} C] [HasColimitsOfSize.{w, w} C]
  (P : L ⥤ K) (A : K ⥤ SimplexCategory ⥤ C)

/-- 元のBK重みから制限重みへの実射を保った、frame実現の添字変更。 -/
def bousfieldKanReindexMap :
    (functor L (P ⋙ A)).obj (bousfieldKanWeight Lᵒᵖ) ⟶
      (functor K A).obj (bousfieldKanWeight Kᵒᵖ) :=
  (functor L (P ⋙ A)).map (bousfieldKanWeightPost P.op) ≫
    reindexMap P A (bousfieldKanWeight Kᵒᵖ)

/-- 任意の標的射への転置は、元の転置を制限して実重み比較を前合成した射。 -/
lemma bousfieldKanReindexMap_homEquiv (Y : C)
    (f : (functor K A).obj (bousfieldKanWeight Kᵒᵖ) ⟶ Y) :
    (adjunction L (P ⋙ A)).homEquiv _ Y (bousfieldKanReindexMap P A ≫ f) =
      bousfieldKanWeightPost P.op ≫
        Functor.whiskerLeft P.op
          ((adjunction K A).homEquiv (bousfieldKanWeight Kᵒᵖ) Y f) ≫
        (homReindexIso P A).hom.app Y := by
  rw [bousfieldKanReindexMap, Category.assoc,
    Adjunction.homEquiv_naturality_left, reindexMap_homEquiv_comp]

end SerrePositivity.DiagramModel.FrameWeightRealization
