module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorComposition

/-!
概要：パラメーターを持つ底上の射の空間から、相対関手へのパラメーター付きの族の関手空間への射。
方針：相対評価の定義域を結合子で並べ替え、相対 curry と通常の curry を順に使う。
規約：底の図式のパラメーター依存は射影で忘れる。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較射の持ち上げの選択独立性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底上のパラメーター付き図式の相対写像空間から、パラメーターを始域とする相対関手空間への関手の空間へ写す。
方針：結合子で相対評価を並べ替え、二段階で curry する。
規約：底の図式 a は L に関して定値。
使われ方：Kerodon Corollary 5.6.0.6、相対的な比較の curry の豊穣的な作用。 -/
def relativeFunctorCurryHom {A E B : SSet.{u}} (p : E ⟶ B) (a : A ⟶ B) (L : SSet.{u}) :
    relativeFunctorSpace p (fst A L ≫ a) ⟶ (ihom L).obj (relativeFunctorSpace p a) :=
  curry (relativeFunctorCurry
    ((α_ A L (relativeFunctorSpace p (fst A L ≫ a))).inv ≫
      relativeFunctorUncurry (𝟙 (relativeFunctorSpace p (fst A L ≫ a)))) (by
    rw [Category.assoc, relativeFunctorUncurry_projection]
    simp only [associator_inv_fst_fst_assoc]))

/-- 概要：相対 curry の豊穣作用は具体的な族の相対頂点を、その相対 curry の関手頂点へ写す。
方針：各次数と各パラメーターで二段階の評価を計算する。
規約：底上の可換性の証明の選択には依存しない。
使われ方：Kerodon Corollary 5.6.0.6、相対頂点間の同型をパラメーター付き比較射の同型へ移す。 -/
lemma relativeFunctorCurryHom_vertex {A E B L : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (H : A ⊗ L ⟶ E) (hH : H ≫ p = fst A L ≫ a) :
    (relativeFunctorCurryHom p a L).app _ (relativeFunctorVertex p (fst A L ≫ a) H hH) =
      functorVertex (relativeFunctorCurry H hH) := by
  apply CategoryTheory.Functor.functorHom_ext
  intro d α
  apply ConcreteCategory.hom_ext
  intro l
  apply Subtype.ext
  apply CategoryTheory.Functor.functorHom_ext
  intro e β
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 概要：底上の二つの族の相対写像空間内での同型は、その相対 curry の関手同型を与える。
方針：相対 curry の豊穣作用で同型を写し、具体的な族の頂点の計算を適用する。
規約：族の底はパラメーター L に関して定値。
使われ方：Kerodon Corollary 5.6.0.6、写像空間の比較射を作る普遍的な持ち上げの選択独立性。 -/
noncomputable def relativeFunctorCurryIso {A E B L : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (H H' : A ⊗ L ⟶ E)
    (hH : H ≫ p = fst A L ≫ a) (hH' : H' ≫ p = fst A L ≫ a)
    (η : VertexIso (relativeFunctorVertex p (fst A L ≫ a) H hH)
      (relativeFunctorVertex p (fst A L ≫ a) H' hH')) :
    FunctorIso (relativeFunctorCurry H hH) (relativeFunctorCurry H' hH') := by
  have h := VertexIso.map η (relativeFunctorCurryHom p a L)
  simpa only [relativeFunctorCurryHom_vertex] using h

end SerrePositivity.InfinityCategories
