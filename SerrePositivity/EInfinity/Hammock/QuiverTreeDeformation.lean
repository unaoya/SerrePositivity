module

public import SerrePositivity.EInfinity.Hammock.QuiverTreeDeformationNaturality

/-!
# 有限木の葉の除去の自然変形

概要：除去して戻す合成関手を元の恒等関手へ自然に比較する。
方針：生成辺での自然性を射列の連結に関する帰納で延長する。
規約：元の接続辺の向きに応じて自然変換の方向を選ぶ。
使われ方：全指定 hammock の有限部分木の縮約。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.QuiverTree
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {T : WideSubquiver (Quiver.Symmetrify Q)}
  [Quiver.Arborescence T] {S : Finset Q} (D : LeafDeletion T S)

def LeafDeletion.positiveDeformation (g : D.parent ⟶ D.leaf)
    (hg : D.edge.val = g.toPos) :
    letI := FiniteQuiver.quiver S
    D.collapseFunctor ⟶ 𝟭 (Paths (FiniteQuiver.Vertex S)) := by
  letI := FiniteQuiver.quiver S
  refine { app := fun x => D.positiveComponent g x, naturality := ?_ }
  intro x y f
  induction f using Paths.induction with
  | id => simp
  | @comp a b c p q ih =>
    change D.collapseFunctor.map p ≫ D.positiveComponent g b =
      D.positiveComponent g a ≫ p at ih
    change D.collapseFunctor.map (p ≫ (Paths.of (FiniteQuiver.Vertex S)).map q) ≫
      D.positiveComponent g c =
      D.positiveComponent g a ≫ (p ≫ (Paths.of (FiniteQuiver.Vertex S)).map q)
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [D.positiveComponent_generator g hg q, ← Category.assoc, ih, Category.assoc]

def LeafDeletion.negativeDeformation (g : D.leaf ⟶ D.parent)
    (hg : D.edge.val = g.toNeg) :
    letI := FiniteQuiver.quiver S
    𝟭 (Paths (FiniteQuiver.Vertex S)) ⟶ D.collapseFunctor := by
  letI := FiniteQuiver.quiver S
  refine { app := fun x => D.negativeComponent g x, naturality := ?_ }
  intro x y f
  induction f using Paths.induction with
  | id => simp
  | @comp a b c p q ih =>
    change p ≫ D.negativeComponent g b =
      D.negativeComponent g a ≫ D.collapseFunctor.map p at ih
    change (p ≫ (Paths.of (FiniteQuiver.Vertex S)).map q) ≫
      D.negativeComponent g c = D.negativeComponent g a ≫
      D.collapseFunctor.map (p ≫ (Paths.of (FiniteQuiver.Vertex S)).map q)
    simp only [CategoryTheory.Functor.map_comp, Category.assoc]
    rw [D.negativeComponent_generator g hg q, ← Category.assoc, ih, Category.assoc]

def LeafDeletion.deformation :
    letI := FiniteQuiver.quiver S
    (D.collapseFunctor ⟶ 𝟭 (Paths (FiniteQuiver.Vertex S))) ⊕
      (𝟭 (Paths (FiniteQuiver.Vertex S)) ⟶ D.collapseFunctor) := by
  letI := FiniteQuiver.quiver S
  generalize hg : (show (D.parent ⟶ D.leaf) ⊕ (D.leaf ⟶ D.parent) from D.edge.val) = e
  cases e with
  | inl g => exact Sum.inl (D.positiveDeformation g hg)
  | inr g => exact Sum.inr (D.negativeDeformation g hg)

lemma LeafDeletion.positiveDeformation_app (g : D.parent ⟶ D.leaf)
    (hg : D.edge.val = g.toPos) (x : FiniteQuiver.Vertex S) :
    letI := FiniteQuiver.quiver S
    (D.positiveDeformation g hg).app ((Paths.of (FiniteQuiver.Vertex S)).obj x) =
      D.positiveComponent g x := rfl

lemma LeafDeletion.negativeDeformation_app (g : D.leaf ⟶ D.parent)
    (hg : D.edge.val = g.toNeg) (x : FiniteQuiver.Vertex S) :
    letI := FiniteQuiver.quiver S
    (D.negativeDeformation g hg).app ((Paths.of (FiniteQuiver.Vertex S)).obj x) =
      D.negativeComponent g x := rfl

end SerrePositivity.EInfinity.Hammock.QuiverTree
