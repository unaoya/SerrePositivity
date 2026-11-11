module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeFunctorCurryIsoPointComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.FunctorFamilyVertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.RelativeFunctorExtensionEndpoint

/-!
概要：既存の指定 curry 同型の一点成分を元の始域の fiber へ制限する。
方針：実際の成分の端点を元の族の制限に揃え、同じ相対前合成の合成則を使う。
規約：指定比較の値と全円柱の類を保持。使われ方：元の三角形比較の fiber 制限。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の族の curry の実頂点は同じ係数での相対制限の実頂点と一致する。 -/
lemma relativeFunctorCurry_vertex_restriction {A E B L : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) (H : A ⊗ L ⟶ E)
    (hH : H ≫ p = fst A L ≫ a) (l : L _⦋0⦌) :
    (relativeFunctorCurry H hH).app (Opposite.op ⦋0⦌) l =
      (relativeFunctorPre p (fst A L ≫ a) (lift (𝟙 A) (SSet.const l))).app (Opposite.op ⦋0⦌)
        (relativeFunctorVertex p (fst A L ≫ a) H hH) :=
  (relativeFunctorCurry_vertex p a H hH l).trans
    (relativeFunctorPre_vertex p (fst A L ≫ a) (lift (𝟙 A) (SSet.const l)) H hH).symm

/-- 元の指定 curry 同型の成分を始域制限しても同じ指定比較の直接制限になる。 -/
lemma relativeFunctorCurryIso_app_pre {A C E B L : SSet.{u}}
    (p : E ⟶ B) (a : A ⟶ B) [Quasicategory L] [Quasicategory (relativeFunctorSpace p a)]
    (H H' : A ⊗ L ⟶ E)
    (hH : H ≫ p = fst A L ≫ a) (hH' : H' ≫ p = fst A L ≫ a)
    (e : VertexIso (relativeFunctorVertex p (fst A L ≫ a) H hH)
      (relativeFunctorVertex p (fst A L ≫ a) H' hH')) (l : L _⦋0⦌) (s : C ⟶ A) :
    HEq
      (VertexIso.map ((relativeFunctorCurryIso p a H H' hH hH' e).app l)
        (relativeFunctorPre p a s))
      (VertexIso.map e
        (relativeFunctorPre p (fst A L ≫ a) (s ≫ lift (𝟙 A) (SSet.const l)))) := by
  have h := vertexIso_map_heq_of_heq
    ((relativeFunctorCurryIso p a H H' hH hH' e).app l)
    (VertexIso.map e (relativeFunctorPre p (fst A L ≫ a) (lift (𝟙 A) (SSet.const l))))
    (relativeFunctorCurry_vertex_restriction p a H hH l)
    (relativeFunctorCurry_vertex_restriction p a H' hH' l)
    (relativeFunctorCurryIso_app p a H H' hH hH' e l) (relativeFunctorPre p a s)
  exact h.trans ((heq_of_eq (vertexIso_map_comp e
    (relativeFunctorPre p (fst A L ≫ a) (lift (𝟙 A) (SSet.const l)))
    (relativeFunctorPre p a s))).trans
      (vertexIso_map_heq e
        (relativeFunctorPre_comp p (fst A L ≫ a) (lift (𝟙 A) (SSet.const l)) s)))

end SerrePositivity.InfinityCategories.F2
