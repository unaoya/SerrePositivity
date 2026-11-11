module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.TerminalSubcomplexCover

/-!
概要：包含順の鎖を、それぞれの終頂点付き部分複体内の単体で実現する空間。
方針：全ての制限がその最後の添字の部分複体に入り、各頂点が指定頂点となる条件を課す。
規約：条件は全ての面と退化に対して保持する。cofinal 性は別工程。
使われ方：包含順の nerve から元の単体集合への整合的な写像。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {I : Type u} [Preorder I] {X : SSet.{u}}

/-- 同じ単体の全ての制限が、鎖の最後の添字の部分複体に入る条件。 -/
def terminalCarrierCondition (A : I → X.Subcomplex) (z : I → X _⦋0⦌)
    {n : SimplexCategory} (x : X.obj (Opposite.op n)) (s : (nerve I).obj (Opposite.op n)) : Prop :=
  (∀ (m : SimplexCategory) (α : m ⟶ n),
    X.map α.op x ∈ (A (s.obj (α.toOrderHom (Fin.last m.len)))).obj (Opposite.op m)) ∧
  ∀ i : Fin (n.len + 1), X.map (SimplexCategory.const ⦋0⦌ n i).op x = z (s.obj i)

/-- 全ての制限と頂点の条件は単体作用で保たれる。 -/
lemma terminalCarrierCondition_map (A : I → X.Subcomplex) (z : I → X _⦋0⦌)
    {m n : SimplexCategory} (β : m ⟶ n)
    {x : X.obj (Opposite.op n)} {s : (nerve I).obj (Opposite.op n)}
    (h : terminalCarrierCondition A z x s) :
    terminalCarrierCondition A z (X.map β.op x) ((nerve I).map β.op s) := by
  constructor
  · intro l α
    change X.map α.op (X.map β.op x) ∈
      (A (s.obj (β.toOrderHom (α.toOrderHom (Fin.last l.len))))).obj _
    rw [← CategoryTheory.Functor.map_comp_apply]
    exact h.1 l (α ≫ β)
  · intro i
    have hh := h.2 (β.toOrderHom i)
    change X.map (SimplexCategory.const ⦋0⦌ m i).op (X.map β.op x) = _
    rw [← CategoryTheory.Functor.map_comp_apply]
    exact hh

/-- 元の積内で、指定した部分複体と頂点の全条件を持つ単体の空間。 -/
def terminalCarrier (A : I → X.Subcomplex) (z : I → X _⦋0⦌) :
    (X ⊗ nerve I).Subcomplex where
  obj _ := {p | terminalCarrierCondition A z p.1 p.2}
  map β _ hp := terminalCarrierCondition_map A z β.unop hp

/-- 同じ鎖を取り出す射影。 -/
def terminalCarrierProjection (A : I → X.Subcomplex) (z : I → X _⦋0⦌) :
    (terminalCarrier A z).toSSet ⟶ nerve I := (terminalCarrier A z).ι ≫ snd _ _

/-- 同じ元の単体を取り出す写像。 -/
def terminalCarrierValue (A : I → X.Subcomplex) (z : I → X _⦋0⦌) :
    (terminalCarrier A z).toSSet ⟶ X := (terminalCarrier A z).ι ≫ fst _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
