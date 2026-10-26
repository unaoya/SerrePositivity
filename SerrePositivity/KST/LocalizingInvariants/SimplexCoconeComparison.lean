module

public import SerrePositivity.KST.LocalizingInvariants.ArrowComparisonPrefixPath
public import SerrePositivity.KST.LocalizingInvariants.SimplexAttachmentEquivalences
public import SerrePositivity.InfinityCategories.HomotopyLimits.CoconeVertexTriangles

/-!
概要：全前段の比較と指定余錐脚の可換四角形から、全余錐図式の同型を構成する。
方針：次辺の比較の共有経路を実構成し、二点 join へ戻して全単体へ貼る。
規約：共有経路の一致は入力にせず、元の前段比較の順方向の射を回収する。
使われ方：c5 の実右分数と厳密終端成分の回収から一段長い商図式を比較する工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

/-- 終端脚の四角形から、共有経路を構成して全余錐の同型を貼り、前段比較を保つ。 -/
lemma exists_simplexCoconeFunctorIso {X : SSet.{u}} [Quasicategory X] {n : ℕ}
    {F G : (Δ[n] : SSet.{u}) ⟶ X} (c : JoinCocone F) (d : JoinCocone G)
    (a : SSet.Edge (X := (ihom (Δ[n] : SSet.{u})).obj X) (functorVertex F) (functorVertex G))
    (w : SSet.Edge c.vertex d.vertex)
    (ha : IsInvertibleEdge a.toTruncated) (hw : IsInvertibleEdge w.toTruncated)
    (hc : Truncated.HomotopyCategory.homMk
          (HomotopyLimits.coconeVertexLeg c (SSet.yonedaEquiv (simplexLastPoint n))).toTruncated ≫
        Truncated.HomotopyCategory.homMk w.toTruncated =
      Truncated.HomotopyCategory.homMk
          (functorEdgeAt a (SSet.yonedaEquiv (simplexLastPoint n))).toTruncated ≫
        Truncated.HomotopyCategory.homMk
          (HomotopyLimits.coconeVertexLeg d (SSet.yonedaEquiv (simplexLastPoint n))).toTruncated) :
    ∃ e : FunctorIso c.val d.val,
      Arrow.mk ((hoFunctor.map ((pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app X)).toFunctor.map
        e.hom) = Arrow.mk (Truncated.HomotopyCategory.homMk a.toTruncated) := by
  let k := SSet.yonedaEquiv (simplexLastPoint.{u} n)
  let f := HomotopyLimits.coconeVertexLeg c k
  let g := HomotopyLimits.coconeVertexLeg d k
  obtain ⟨b, hbi, hbs⟩ := exists_arrowComparison_preservingPrefixPath a
    (simplexLastPoint n) f g w ha hw hc
  have hf : (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm f.edge =
      joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ c.val := by
    change (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv
      ((joinStdSimplexIso 0 0).inv ≫
        joinMap (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (simplexLastPoint n)))
          (𝟙 Δ[0]) ≫ c.val)) = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  have hg : (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm g.edge =
      joinMap (simplexLastPoint n) (𝟙 Δ[0]) ≫ d.val := by
    change (joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv
      ((joinStdSimplexIso 0 0).inv ≫
        joinMap (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (simplexLastPoint n)))
          (𝟙 Δ[0]) ≫ d.val)) = _
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  let a' := a.ofEq (congrArg functorVertex c.property).symm
    (congrArg functorVertex d.property).symm
  let b₀ := SSet.Edge.ofTruncated (X := (ihom (join (Δ[0] : SSet.{u}) Δ[0])).obj X)
    (b.map ((truncation 2).map
    ((pre (joinStdSimplexIso.{u} 0 0).hom).app X)))
  let b' := b₀.ofEq (congrArg functorVertex hf) (congrArg functorVertex hg)
  have ha' : IsInvertibleEdge a'.toTruncated :=
    (isInvertibleEdge_congr (e := a.toTruncated) (f := a'.toTruncated) rfl).mp ha
  have hb' : IsInvertibleEdge b'.toTruncated :=
    (isInvertibleEdge_congr (e := b₀.toTruncated) (f := b'.toTruncated) rfl).mp
      (hbi.map ((pre (joinStdSimplexIso 0 0).hom).app X))
  have hs : SSet.yonedaEquiv.symm a'.edge ≫ (pre (simplexLastPoint n)).app X =
      SSet.yonedaEquiv.symm b'.edge ≫ (pre (joinInl (Δ[0] : SSet.{u}) Δ[0])).app X := by
    have haraw : a'.edge = a.edge := rfl
    have hbraw : b'.edge = ((pre (joinStdSimplexIso 0 0).hom).app X).app
        (Opposite.op ⦋1⦌) b.edge := rfl
    rw [haraw, hbraw]
    have hm : SSet.yonedaEquiv.symm b'.edge = SSet.yonedaEquiv.symm b.edge ≫
        (pre (joinStdSimplexIso 0 0).hom).app X := by
      rw [hbraw, ← SSet.yonedaEquiv_symm_comp]
      rfl
    rw [← hbraw, hm, Category.assoc, ← NatTrans.comp_app, ← pre_map,
      joinStdSimplexIso_zero_inl]
    exact hbs.symm
  obtain ⟨e, he, _⟩ := exists_simplexAttachmentFunctorIso n c.val d.val
    a'.toTruncated b'.toTruncated hs ha' hb'
  refine ⟨e, he.trans ?_⟩
  exact Truncated.HomotopyCategory.congr_arrowMk_homMk a'.toTruncated a.toTruncated rfl

end SerrePositivity.KST.LocalizingInvariants
