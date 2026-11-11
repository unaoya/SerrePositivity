module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.RelativeFunctorExtensionSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.RelativeFunctorPostcomposition

/-!
概要：底を保つ全空間の射で、初期値を固定した相対延長空間を後合成する。
方針：相対後合成の制限自然性から、同じ初期値の像の fiber へ持ち上げる。
規約：元の全延長とその像を保持。使われ方：指定輸送比較の後合成自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {A D E F B : SSet.{u}} (p : E ⟶ B) (q : F ⟶ B)
  (f : E ⟶ F) (hf : f ≫ q = p) (b : A ⟶ B) (i : D ⟶ A)
  (v : D ⟶ E) (hv : v ≫ p = i ≫ b)

include p hf hv in
/-- 元の初期値を後合成した像は同じ底を被覆する。 -/
lemma relativeExtensionPost_initial_base : (v ≫ f) ≫ q = i ≫ b := by
  rw [Category.assoc, hf, hv]

/-- 全相対延長を、同じ初期値の像を固定した全相対延長へ送る。 -/
def relativeExtensionPost :
    relativeFunctorExtensionSpace p b i v hv ⟶
      relativeFunctorExtensionSpace q b i (v ≫ f)
        (relativeExtensionPost_initial_base p q f hf b i v hv) :=
  vertexFiberLift _ _
    (relativeFunctorExtensionSpaceι p b i v hv ≫ relativeFunctorPost p q f hf b) (by
      rw [Category.assoc, relativeFunctorPost_pre, ← Category.assoc,
        relativeFunctorExtensionSpaceι_pre, SSet.const_comp]
      congr 1)

/-- 包含後は元の全延長の相対後合成そのもの。 -/
lemma relativeExtensionPost_ι :
    relativeExtensionPost p q f hf b i v hv ≫
      relativeFunctorExtensionSpaceι q b i (v ≫ f)
        (relativeExtensionPost_initial_base p q f hf b i v hv) =
      relativeFunctorExtensionSpaceι p b i v hv ≫ relativeFunctorPost p q f hf b := rfl

/-- 元の実延長の頂点は、その同じ実延長の後合成の頂点へ送られる。 -/
lemma relativeExtensionPost_vertex (W : A ⟶ E) (hW : W ≫ p = b) (hWi : i ≫ W = v) :
    (relativeExtensionPost p q f hf b i v hv).app (Opposite.op ⦋0⦌)
      (relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W, hW, hWi⟩) =
        relativeFunctorExtensionSpaceVertexEquiv q b i (v ≫ f)
          (relativeExtensionPost_initial_base p q f hf b i v hv)
          ⟨W ≫ f, by rw [Category.assoc, hf, hW],
            by rw [← Category.assoc, hWi]⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SerrePositivity.InfinityCategories.F2
