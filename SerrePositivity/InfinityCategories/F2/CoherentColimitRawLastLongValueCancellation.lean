module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawLastPointActionValue

/-!
概要：元の長辺残余の消去式を、同じ実始域射と値射で写した指定比較の等式として保持する。
方針：元の消去等式の前後合成に、同じ指定同型の合成と逆の関手性を使う。
規約：元の全三角形・三比較・実射を保持。使われ方：a6 の模型三角形式への代入。
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

/-- 同じ前後合成後も、元の長辺残余と最後辺指定比較は新長辺残余の逆へ厳密に消去される。 -/
lemma coherentColimitRawLastLong_inverse_middle_cancel_precomp_postcomp
    {A X : SSet.{u + 1}} (f : A ⟶ leftUnstraightening (coherentColimitRawConstantDiagram B F))
    (g : vertexFiber pointedSpaceProjection
      (JoinCocone.vertex (coherentDiagramTotalCocone J)) ⟶ X) :
    (((coherentColimitConstantTriangleRemainderIso B T).precomp f).postcomp g).symm ≪≫
      (((coherentColimitRawLastPointActionIso B a b).precomp f).postcomp g) =
    (((coherentColimitRawLastLongRemainderIso B T).precomp f).postcomp g).symm := by
  have h := congrArg (fun e => (FunctorIso.precomp e f).postcomp g)
    (coherentColimitRawLastLong_inverse_middle_cancel B T)
  simpa only [functorIso_precomp_trans, functorIso_postcomp_trans,
    functorIso_precomp_symm, functorIso_postcomp_symm] using h

end SerrePositivity.InfinityCategories.F2
