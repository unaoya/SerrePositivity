module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamilyProjection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.FunctorHomCongrArrow

/-!
概要：元の固定図式の錐の関手圏の比較射を、端点表示に依存しない矢印として元の極限比較へ戻す。
方針：既存のslice比較の零次成分の等式で同じ射を移し、既存の頂点射影の法則を使う。
規約：HTT §1.2.13、Kerodon Example 4.6.6.8（Tag 04J5）の既存比較の計算法則。
使われ方：S8 の指定輸送の終点比較を、元の固定された極限頂点の同型へ戻す。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 元の錐の関手圏の任意の比較射の頂点は、矢印として同じ標準極限比較になる。 -/
lemma limitVertexIso_coneFamily_arrow {K X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ X} (c d : JoinCone p) (hc : IsLimitCone c) (hd : IsLimitCone d)
    (m : (HomotopyCategory.mk (coneFamilyVertexEquiv p c) : hoFunctor.obj (coneFamily p)) ⟶
      HomotopyCategory.mk (coneFamilyVertexEquiv p d)) :
    Arrow.mk ((hoFunctor.map (coneFamilyApex p)).toFunctor.map m) =
      Arrow.mk (limitVertexIso c d hc hd).hom := by
  let hC := sliceConeFamilyMap_app_zero p c
  let hD := sliceConeFamilyMap_app_zero p d
  let m0 : (HomotopyCategory.mk ((sliceConeFamilyMap p).app _ c) :
      hoFunctor.obj (coneFamily p)) ⟶ HomotopyCategory.mk ((sliceConeFamilyMap p).app _ d) :=
    eqToHom (congrArg (fun v => (HomotopyCategory.mk v : hoFunctor.obj (coneFamily p))) hC) ≫ m ≫
      eqToHom (congrArg (fun v => (HomotopyCategory.mk v : hoFunctor.obj (coneFamily p))) hD.symm)
  have h := congrArg Arrow.mk (limitVertexIso_coneFamily_projection c d hc hd m0)
  simp only [Arrow.arrow_mk_comp_eqToHom, Arrow.arrow_mk_eqToHom_comp] at h
  have hm : Arrow.mk ((hoFunctor.map (coneFamilyApex p)).toFunctor.map m0) =
      Arrow.mk ((hoFunctor.map (coneFamilyApex p)).toFunctor.map m) := by
    simp only [m0, Functor.map_comp, eqToHom_map,
      Arrow.arrow_mk_comp_eqToHom, Arrow.arrow_mk_eqToHom_comp]
  exact hm.symm.trans h

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
