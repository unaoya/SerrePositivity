module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorVertices

/-!
概要：底と両端の実図式の等式で、元の相対頂点同型の表示だけを変更する。
方針：三つの等式を消去し、同じ相対頂点同型を返す。
規約：元の指定同型の値を保持。使われ方：全三角形比較の三面の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 底と両端の実際の図式の表示だけを変えた、同じ相対頂点同型。 -/
def relativeVertexIsoOfEq {A E B : SSet.{u}} (p : E ⟶ B)
    {a a' : A ⟶ B} {f g f' g' : A ⟶ E}
    {hf : f ≫ p = a} {hg : g ≫ p = a}
    (e : VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg))
    (ha : a = a') (hs : f = f') (ht : g = g')
    (hf' : f' ≫ p = a' :=
      (congrArg (fun W => W ≫ p) hs).symm.trans (hf.trans ha))
    (hg' : g' ≫ p = a' :=
      (congrArg (fun W => W ≫ p) ht).symm.trans (hg.trans ha)) :
    VertexIso (relativeFunctorVertex p a' f' hf')
      (relativeFunctorVertex p a' g' hg') := by
  subst a' f' g'
  exact e

/-- 元の底と実両端を等式で移送した後も、指定同型の値は変更しない。 -/
lemma relativeVertexIsoOfEq_heq {A E B : SSet.{u}} (p : E ⟶ B)
    {a a' : A ⟶ B} {f g f' g' : A ⟶ E}
    {hf : f ≫ p = a} {hg : g ≫ p = a}
    (e : VertexIso (relativeFunctorVertex p a f hf) (relativeFunctorVertex p a g hg))
    (ha : a = a') (hs : f = f') (ht : g = g')
    (hf' : f' ≫ p = a' :=
      (congrArg (fun W => W ≫ p) hs).symm.trans (hf.trans ha))
    (hg' : g' ≫ p = a' :=
      (congrArg (fun W => W ≫ p) ht).symm.trans (hg.trans ha)) :
    HEq (relativeVertexIsoOfEq p e ha hs ht hf' hg') e := by
  subst a' f' g'
  rfl

end SerrePositivity.InfinityCategories.F2
