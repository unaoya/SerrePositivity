module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawLastLongFactorization
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：元の新長辺残余の逆を、任意の実前後合成後も元の二つの逆比較へ分解する。
方針：元の正規化の実両端を保持し、指定比較の逆と前後合成の関手性を使う。
規約：元の残余・第一辺比較・普遍三角形を保持。使われ方：元の模型三角形式への代入。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {a : SSet.Homotopy F G} {b : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle a b d)

/-- 元の残余の逆は、実前後合成後も同じ普遍二辺比較と第一辺比較の逆の合成になる。 -/
lemma coherentColimitRawLastLong_inverse_factorization_precomp_postcomp
    {A X : SSet.{u + 1}} (f : A ⟶ leftUnstraightening (coherentColimitRawConstantDiagram B F))
    (g : vertexFiber pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone J)) ⟶ X) :
    HEq (((coherentColimitRawLastLongRemainderIso B T).precomp f).postcomp g).symm
      ((((coherentColimitRawUniversalTriangleComparison B T
          (coherentColimitRawConstantFiberProjection B F)).precomp f).postcomp g).symm ≪≫
        ((((coherentColimitConstantTransportRawPointIso B a).postcomp
          (coherentColimitRawFiberTransport B b)).precomp f).postcomp g).symm) := by
  have he := functorIsoOfEq_symm_precomp_postcomp_heq
    (coherentColimitRawLastLongRemainderIso B T) rfl
    (coherentColimitConstantTransport_raw_point_target B d) f g
  change HEq ((FunctorIso.precomp
    (coherentColimitRawLastLongNormalizedRemainderIso B T).symm f).postcomp g) _ at he
  rw [coherentColimitRawLastLongNormalizedRemainderIso_eq_factorization,
    Iso.trans_symm, functorIso_precomp_trans, functorIso_postcomp_trans,
    functorIso_precomp_symm, functorIso_postcomp_symm,
    functorIso_precomp_symm, functorIso_postcomp_symm] at he
  simpa only [functorIso_precomp_symm, functorIso_postcomp_symm] using he.symm

end SerrePositivity.InfinityCategories.F2
