module

public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeInternalHomTrivialFibration

/-!
概要：anodyne射とKan fibrationの相対内部Homは自明Kan fibration。
方針：既存のpushout-productのanodyne性を二変数随伴で移す。
使われ方：HTT 4.2.4.4、RR02(a)のBK重みに対する相対持ち上げの計算。
規約：SSetのモデル構造の存在を仮定しない。
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed HomotopicalAlgebra SSet
open scoped SSet.modelCategoryQuillen
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
namespace SerrePositivity.SimplicialModel

/-- anodyneな左因子に対する、既存の二変数随伴の境界持ち上げ法則。 -/
lemma anodyne_pullbackHom_trivialKanFibration {A B E Y : SSet.{u}}
    (i : A ⟶ B) (hi : anodyneExtensions i) (p : E ⟶ Y) [Fibration p]
    (sq' : internalHom.PullbackObjObj i p) : TrivialKanFibration sq'.π := by
  apply (trivialKanFibration_iff_boundary _).mpr
  intro n
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) i (boundary n).ι
  rw [← internalHomAdjunction₂.hasLiftingProperty_iff sq sq']
  exact (anodyneExtensions_pushoutObjObjι' sq hi) p
    ((HomotopicalAlgebra.fibration_iff p).mp inferInstance)

end SerrePositivity.SimplicialModel
