module

public import SerrePositivity.InfinityCategories.F2.Presentable.Supply.SectionBaseChangeReindex

/-!
概要：指定された関手同型の転置と合成・添字制限の両立。
方針：内部 Hom 交換の実写像を正規化 Hom 作用へ送る。
規約：元の同型をそのまま転置する。
使われ方：P-12 の切断実現から単体切断同型への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：指定された全自然変換を二変数交換する。
方針：同じ内部 Hom 交換射の Hom 作用を正規化する。
規約：可逆性を要求しない。使われ方：指定同型の転置の Hom 計算。 -/
def transposeFunctorHom {A I X : SSet.{u}} {F G : A ⟶ (ihom I).obj X}
    (α : FunctorHom F G) : FunctorHom (transposeFunctorFamily F) (transposeFunctorFamily G) :=
  normalizedVertexHomMap (internalHomSwapIso A I X).hom rfl rfl α

/-- 概要：元の指定同型を転置した順方向は元の Hom の転置。
方針：交換射による同型の像を展開する。
規約：元の同型を保持する。使われ方：転置の合成の計算。 -/
lemma functorIsoTranspose_hom {A I X : SSet.{u}} {F G : A ⟶ (ihom I).obj X}
    (e : FunctorIso F G) : e.transpose.hom = transposeFunctorHom e.hom := by
  simp only [FunctorIso.transpose, VertexIso.map, transposeFunctorHom, normalizedVertexHomMap,
    eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：指定同型の転置は同じ中間関手を持つ合成を保存する。
方針：元のホモトピー圏の関手の合成則を使う。
規約：元の全図式の同型の等式。使われ方：単体切断の合成則。 -/
lemma functorIsoTranspose_trans {A I X : SSet.{u}} {F G H : A ⟶ (ihom I).obj X}
    (e : FunctorIso F G) (d : FunctorIso G H) :
    FunctorIso.transpose (e ≪≫ d) = e.transpose ≪≫ d.transpose := by
  apply Iso.ext
  simp only [functorIsoTranspose_hom, Iso.trans_hom, transposeFunctorHom]
  exact normalizedVertexHomMap_hom_comp _ _ _ _ e.hom d.hom

/-- 概要：元の関手等式による同型移送は転置と両立する。
方針：二つの端点等式を消去する。
規約：指定同型を保持する。使われ方：単体切断の端点正規化。 -/
lemma diagramIsoCongr_transpose {A I X : SSet.{u}}
    {F G F' G' : A ⟶ (ihom I).obj X} (hF : F = F') (hG : G = G')
    (e : FunctorIso F G) :
    (diagramIsoCongr hF hG e).transpose =
      diagramIsoCongr (congrArg transposeFunctorFamily hF) (congrArg transposeFunctorFamily hG)
        e.transpose := by
  subst F' G'
  simp only [diagramIsoCongr, eqToIso_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_refl]

/-- 概要：全自然変換の転置は内部 Hom の添字制限を始域制限へ移す。
方針：交換射と制限射の厳密な可換式を Hom 作用へ送る。
規約：元の射を保持する。使われ方：指定実現同型の添字制限の転置。 -/
lemma transposeFunctorHom_postcomp_pre {A I J X : SSet.{u}} (q : J ⟶ I)
    {F G : A ⟶ (ihom I).obj X} (α : FunctorHom F G) :
    F1B.kanFunctorHomCongr (transposeFunctorFamily_pre F q) (transposeFunctorFamily_pre G q)
      (transposeFunctorHom (postcomposeFunctorHom ((pre q).app X) α)) =
      precomposeFunctorHom q (transposeFunctorHom α) := by
  unfold transposeFunctorHom
  rw [kanFunctorHomCongr_normalizedMap]
  unfold postcomposeFunctorHom precomposeFunctorHom
  rw [normalizedVertexHomMap_comp, normalizedVertexHomMap_comp]
  have hm : HEq
      ((hoFunctor.map ((ihom A).map ((pre q).app X) ≫
        (internalHomSwapIso A J X).hom)).toFunctor.map α)
      ((hoFunctor.map ((internalHomSwapIso A I X).hom ≫
        (pre q).app ((ihom A).obj X))).toFunctor.map α) := by
    rw [internalHomSwapIso_pre]
  exact eq_of_heq ((normalizedVertexHomMap_heq _ _ _ α).trans
    (hm.trans (normalizedVertexHomMap_heq _ _ _ α).symm))

/-- 概要：指定同型の転置は内部 Hom の制限を同じ始域制限へ移す。
方針：元の Hom の転置の制限公式を使う。
規約：指定された元の同型の等式。使われ方：単体切断の添字制限との照合。 -/
lemma functorIsoTranspose_postcomp_pre {A I J X : SSet.{u}} (q : J ⟶ I)
    {F G : A ⟶ (ihom I).obj X} (e : FunctorIso F G) :
    diagramIsoCongr (transposeFunctorFamily_pre F q) (transposeFunctorFamily_pre G q)
      ((e.postcomp ((pre q).app X)).transpose) = e.transpose.precomp q := by
  apply Iso.ext
  rw [diagramIsoCongr_hom, functorIsoTranspose_hom, functorIsoPostcomp_hom,
    functorIsoPrecomp_hom, functorIsoTranspose_hom]
  exact transposeFunctorHom_postcomp_pre q e.hom

end SerrePositivity.InfinityCategories.F2.Presentable
