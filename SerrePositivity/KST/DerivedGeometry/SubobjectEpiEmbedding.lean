module

public import Mathlib.CategoryTheory.Abelian.Subobject

/-!
概要：全射の終域の部分対象を始域の部分対象の集合へ埋め込む。
方針：アーベル圏の部分対象・商の双対性と、反対圏の単射による部分対象の埋め込みを使う。
規約：対象の濃度を別途仮定せず、実際の集合の単射を構成する。
使われ方：Stacks Lemma 19.12.1・19.12.2、TT §3・§8、Toën §3.2 の小さい試験族の上界。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits Opposite
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type*} [Category* C] [Abelian C] {M N : C} (p : M ⟶ N) [Epi p]

/--
概要：全射の終域の部分対象集合から始域の部分対象集合への埋め込み。
方針：部分対象・商の双対性で単射による部分対象の埋め込みに帰着する。
規約：集合の埋め込みとして濃度の上界に用いる。
使われ方：Stacks 19.12.1・19.12.2、TT §3 の帰納的な部分対象集合の上界。
-/
def subobjectEpiEmbedding : Subobject N ↪ Subobject M where
  toFun S := (Abelian.subobjectIsoSubobjectOp M).symm
    ((Subobject.map p.op).obj ((Abelian.subobjectIsoSubobjectOp N) S))
  inj' S T h := by
    apply (Abelian.subobjectIsoSubobjectOp N).injective
    apply Subobject.map_obj_injective p.op
    exact (Abelian.subobjectIsoSubobjectOp M).symm.injective h

end SerrePositivity.KST.DerivedGeometry
