module
public import SerrePositivity.InfinityCategories.Core.VertexFiber

/-!
概要：二つの厳密 fiber の順序交換と射の等式による輸送。
方針：元の全単体と比較円柱を保ち、厳密 fiber の普遍性で接続する。
規約：安定性を先取りしない。使われ方：一般安定性判定の実 loop fiber 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 二つの厳密 fiber を取る順序は、元の単体を保つ同型で交換できる。 -/
def vertexFiberSwapIso {A B C : SSet.{u}} (p : A ⟶ B) (q : A ⟶ C)
    (b : B _⦋0⦌) (c : C _⦋0⦌) :
    vertexFiber (vertexFiberι p b ≫ q) c ≅ vertexFiber (vertexFiberι q c ≫ p) b where
  hom := {
    app _ := ↾fun s ↦ ⟨⟨s.val.val, s.property⟩, s.val.property⟩
    naturality {_ _} _ := rfl }
  inv := {
    app _ := ↾fun s ↦ ⟨⟨s.val.val, s.property⟩, s.val.property⟩
    naturality {_ _} _ := rfl }
  hom_inv_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    rfl

/-- 厳密 fiber の順序交換は、元の全空間への二重の包含と可換。 -/
lemma vertexFiberSwapIso_hom_ι {A B C : SSet.{u}} (p : A ⟶ B) (q : A ⟶ C)
    (b : B _⦋0⦌) (c : C _⦋0⦌) :
    (vertexFiberSwapIso p q b c).hom ≫ vertexFiberι (vertexFiberι q c ≫ p) b ≫
      vertexFiberι q c = vertexFiberι (vertexFiberι p b ≫ q) c ≫ vertexFiberι p b := rfl
/-- 射の等式による厳密 fiber の輸送は、元の全空間への包含を保つ。 -/
lemma vertexFiberEqToIso_hom_ι {E B : SSet.{u}} {p q : E ⟶ B} (h : p = q)
    (b : B _⦋0⦌) :
    (eqToIso (congrArg (fun f ↦ vertexFiber f b) h)).hom ≫ vertexFiberι q b =
      vertexFiberι p b := by
  cases h
  simp

end SerrePositivity.InfinityCategories
