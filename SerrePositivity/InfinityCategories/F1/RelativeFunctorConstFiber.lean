module

public import SerrePositivity.InfinityCategories.F1.RelativeFunctorVertices

/-!
概要：底の一点に定値な相対関手を、その fiber への関手にする。
方針：相対評価の底の固定条件を使って fiber に持ち上げてから curry する。
規約：射影の充填性は不要。
使われ方：Kerodon Proposition 5.2.2.8、相対持ち上げの終点の比較を fiber 内の関手同型へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底の一点に定値な相対関手空間から fiber への内部 Hom へ写す。
方針：普遍的な相対評価を fiber に持ち上げて curry する。
規約：定義域 A は任意。
使われ方：Kerodon Proposition 5.2.2.8、終点の相対頂点同型を fiber 内で読む。 -/
def relativeFunctorConstFiberHom {A E B : SSet.{u}} (p : E ⟶ B) (b : B _⦋0⦌) :
    relativeFunctorSpace p (SSet.const b : A ⟶ B) ⟶ (ihom A).obj (vertexFiber p b) :=
  curry (vertexFiberLift p b (relativeFunctorUncurry (𝟙 _)) (by
    rw [relativeFunctorUncurry_projection, SSet.comp_const]))

/-- 概要：fiber への通常の射の相対頂点は、その射の関手頂点へ写る。
方針：内部 Hom の各成分の fiber の部分型の値を計算する。
規約：fiber の包含への後合成を相対頂点として表示する。
使われ方：Kerodon Proposition 5.2.2.8、具体的な終点の射の比較への移行。 -/
lemma relativeFunctorConstFiberHom_vertex {A E B : SSet.{u}}
    (p : E ⟶ B) (b : B _⦋0⦌) (g : A ⟶ vertexFiber p b) :
    (relativeFunctorConstFiberHom (A := A) p b).app _
      (relativeFunctorVertex p (SSet.const b) (g ≫ vertexFiberι p b) (by
        rw [Category.assoc, vertexFiberι_comp, SSet.comp_const])) = functorVertex g := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro a
  apply Subtype.ext
  rfl

end SerrePositivity.InfinityCategories
