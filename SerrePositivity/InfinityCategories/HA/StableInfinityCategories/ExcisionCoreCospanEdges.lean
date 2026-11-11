module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanToHorn
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismFilling
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetClosureRetraction

/-!
概要：比較格子の穿孔 core と元の cospan の実極限を比較する。
方針：固定した初期収縮と標準ホーンの全単体同型を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

def excisionCoreCospanPoint (i j : Fin 2) (h : 1 ≤ i.val + j.val) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanIndex.{u} :=
  ⟨⟨_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.excisionGridCorePoint i.castSucc j.castSucc, h⟩, by
    change i.val ≤ 1 ∧ j.val ≤ 1
    constructor <;> omega⟩

def excisionCoreCospanFirstEdge : (Δ[1] : SSet.{u}) ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanIndex.{u} where
  app n := ↾fun s ↦
    (⟨fun k ↦ excisionCoreCospanPoint 1 ((stdSimplex.objEquiv s).toOrderHom k) (by omega),
      fun _ _ h ↦ ⟨le_rfl, (stdSimplex.objEquiv s).toOrderHom.monotone h⟩⟩ :
      Fin (n.unop.len + 1) →o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanIndex.{u}).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

def excisionCoreCospanSecondEdge : (Δ[1] : SSet.{u}) ⟶
    nerve _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanIndex.{u} where
  app n := ↾fun s ↦
    (⟨fun k ↦ excisionCoreCospanPoint ((stdSimplex.objEquiv s).toOrderHom k) 1 (by omega),
      fun _ _ h ↦ ⟨(stdSimplex.objEquiv s).toOrderHom.monotone h, le_rfl⟩⟩ :
      Fin (n.unop.len + 1) →o _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionCoreCospanIndex.{u}).toFunctor
  naturality := by
    intro n m α
    apply ConcreteCategory.hom_ext
    intro s
    apply CategoryTheory.Functor.ext
    · intro i j f; apply Subsingleton.elim
    · intro i; rfl

lemma excisionCoreCospanEdges_target :
    stdSimplex.δ (0 : Fin 2) ≫ excisionCoreCospanFirstEdge.{u} =
      stdSimplex.δ (0 : Fin 2) ≫ excisionCoreCospanSecondEdge := by
  apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.thinNerveHom_ext_of_vertices
  intro v
  obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
  fin_cases i
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply ULift.ext
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> decide

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
