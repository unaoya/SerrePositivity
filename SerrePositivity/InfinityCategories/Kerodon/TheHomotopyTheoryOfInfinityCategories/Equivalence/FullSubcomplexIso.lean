module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalVertices

/-!
概要：単体集合の同型に対応する頂点条件の全部分複体の同型。
方針：同型と逆同型を条件付きの全部分複体に持ち上げる。
規約：頂点条件は同値として指定する。
使われ方：Kerodon §4.5.3（Tag 032Y）、§4.5.5（Tag 01F6） の内部 Hom と可逆な path の比較。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：同型で対応する頂点条件の全部分複体は同型。
方針：元の同型の両向きを持ち上げ、逆性を各単体の値で検査する。
規約：quasicategory 性は不要。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆な path の内部 Hom との比較。 -/
def fullSubcomplexIso {X Y : SSet.{u}} (e : X ≅ Y)
    (P : X _⦋0⦌ → Prop) (Q : Y _⦋0⦌ → Prop)
    (h : ∀ x : X _⦋0⦌, P x ↔ Q (e.hom.app (Opposite.op ⦋0⦌) x)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P : SSet.{u}) ≅ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q : SSet.{u}) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift Q ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫ e.hom) (fun v ↦
    (h v.val).mp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v))
  inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q).ι ≫ e.inv) (by
    intro v
    apply (h (e.inv.app (Opposite.op ⦋0⦌) v.val)).mpr
    have he := congrArg (fun f : Y ⟶ Y ↦ f.app (Opposite.op ⦋0⦌) v.val) e.inv_hom_id
    change e.hom.app (Opposite.op ⦋0⦌) (e.inv.app (Opposite.op ⦋0⦌) v.val) = v.val at he
    rw [he]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex v)
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    exact congrArg (fun f : X ⟶ X ↦ f.app n v.val) e.hom_inv_id
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    exact congrArg (fun f : Y ⟶ Y ↦ f.app n v.val) e.inv_hom_id

/-- 概要：全部分複体の同型の順方向は元の同型の制限。
方針：持ち上げの包含上の計算を使う。
規約：頂点条件の証明には依存しない。
使われ方：Kerodon §4.5.3（Tag 032Y） の内部 Hom との比較。 -/
lemma fullSubcomplexIso_hom_ι {X Y : SSet.{u}} (e : X ≅ Y)
    (P : X _⦋0⦌ → Prop) (Q : Y _⦋0⦌ → Prop)
    (h : ∀ x : X _⦋0⦌, P x ↔ Q (e.hom.app (Opposite.op ⦋0⦌) x)) :
    (fullSubcomplexIso e P Q h).hom ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices Y Q).ι =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices X P).ι ≫ e.hom := rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
