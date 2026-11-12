module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.VertexRetractions

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import Mathlib.CategoryTheory.Retract
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：頂点条件の元の ∞ 圏内での retract 閉包を定義する。
方針：ホモトピー圏の元の頂点間の射と分裂等式を使用する。
規約：同じ頂点を保持し、coherent な分裂の存在との同値は別に証明する。
使われ方：HTT 5.1.4.2 の前層内の retract 閉包の構成。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion
open _root_.SerrePositivity.InfinityCategories

/-- 元の頂点条件の、同じ ∞ 圏内での retract 閉包。 -/
def retractClosure {X : SSet.{u}} (P : X _⦋0⦌ → Prop) (x : X _⦋0⦌) : Prop :=
  ∃ y, P y ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x y

/-- retract 閉包は元の対象条件を含む。 -/
lemma mem_retractClosure {X : SSet.{u}} {P : X _⦋0⦌ → Prop} {x : X _⦋0⦌}
    (h : P x) : retractClosure P x := ⟨x, h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.refl x⟩

/-- 元の条件の包含は、その retract 閉包の包含を与える。 -/
lemma retractClosure_mono {X : SSet.{u}} {P Q : X _⦋0⦌ → Prop}
    (h : ∀ x, P x → Q x) {x : X _⦋0⦌} : retractClosure P x → retractClosure Q x := by
  rintro ⟨y, hy, hxy⟩
  exact ⟨y, h y hy, hxy⟩

/-- 元の retract 閉包は retract に関して閉じている。 -/
lemma retractClosure_of_retract {X : SSet.{u}} {P : X _⦋0⦌ → Prop}
    {x y : X _⦋0⦌} (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf x y) (hy : retractClosure P y) :
    retractClosure P x := by
  obtain ⟨z, hz, hyz⟩ := hy
  exact ⟨z, hz, h.trans hyz⟩

/-- retract 閉包は冪等。 -/
lemma retractClosure_idempotent {X : SSet.{u}} (P : X _⦋0⦌ → Prop) (x : X _⦋0⦌) :
    retractClosure (retractClosure P) x ↔ retractClosure P x := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    exact retractClosure_of_retract hxy hy
  · exact mem_retractClosure

/-- 元の retract 閉包の所属は元の頂点同型で不変。 -/
lemma retractClosure_iff_of_iso {X : SSet.{u}} (P : X _⦋0⦌ → Prop)
    {x y : X _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y) : retractClosure P x ↔ retractClosure P y := by
  constructor
  · exact retractClosure_of_retract (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso e.symm)
  · exact retractClosure_of_retract (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf.of_iso e)

end SerrePositivity.InfinityCategories.HTT.RetractsAndIdempotentCompletion
