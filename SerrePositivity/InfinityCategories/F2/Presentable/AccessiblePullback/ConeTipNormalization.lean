module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.NormalizedSourcePresentation

/-!
概要：一段の因子化から、同じ元の終点を持つ入力付き表示を回収する。
方針：右余錐頂点への自明 Kan 制限に、元の比較辺を指定終点として持ち上げる。
規約：入力図式と元の比較辺を全単体上で保持する。
使われ方：元の成分表示の入力付き正規化の具体的な接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：固定余錐の全下方図式を同じ余錐頂点の下へ制限する。
方針：右余錐頂点へ制限し、指定した点射へ等号で移す。
規約：元の余錐の全構造射を使う。
使われ方：元の一段の表示から入力付き表示を作る。 -/
def coneTipRestriction {K C : SSet.{u}} {q : K ⟶ C} (w : JoinCocone q)
    (p : (Δ[0] : SSet.{u}) ⟶ C) (h : joinInr K Δ[0] ≫ w.val = p) :
    sliceUnder w.val ⟶ sliceUnder p :=
  sliceUnderRestrict w.val (joinInr K Δ[0]) ≫ (eqToIso (congrArg sliceUnder h)).hom

/-- 概要：固定余錐の頂点への制限は自明 Kan。
方針：許可済みの元の右余錐点の right anodyne 性と等号同型を使う。
規約：固定入力形状の有限性は不要。
使われ方：元の終点を固定した表示全体の持ち上げ。 -/
lemma coneTipRestriction_trivialKanFibration {K C : SSet.{u}} [Quasicategory C]
    {q : K ⟶ C} (w : JoinCocone q) (p : (Δ[0] : SSet.{u}) ⟶ C)
    (h : joinInr K Δ[0] ≫ w.val = p) : TrivialKanFibration (coneTipRestriction w p h) := by
  have hr := sliceUnderRestrict_trivialKanFibration w.val (joinInr K Δ[0])
    (Ind.coneTip_rightAnodyne K)
  exact ⟨trivialKanFibrations.comp_mem _ _ hr.mem
    (trivialKanFibrations.of_isIso (eqToIso (congrArg sliceUnder h)).hom)⟩

/-- 概要：固定余錐の頂点への制限は元の底の終点を保持する。
方針：等号移送と始域制限の射影公式を使う。
規約：元の全射影の等式。
使われ方：正規化した表示の元の底の図式の回収。 -/
lemma coneTipRestriction_projection {K C : SSet.{u}} {q : K ⟶ C} (w : JoinCocone q)
    (p : (Δ[0] : SSet.{u}) ⟶ C) (h : joinInr K Δ[0] ≫ w.val = p) :
    coneTipRestriction w p h ≫ sliceUnderProjection p = sliceUnderProjection w.val := by
  have hep {A X : SSet.{u}} {f g : A ⟶ X} (h : f = g) :
      (eqToIso (congrArg sliceUnder h)).hom ≫ sliceUnderProjection g =
        sliceUnderProjection f := by
    subst g
    rfl
  rw [coneTipRestriction, Category.assoc, hep h, sliceUnderRestrict_projection]

/-- 概要：元の比較辺から得た全余錐の頂点制限は元の底の比較辺。
方針：等号輸送の値を消して元の全二頂点面を回収する。
規約：元の実際の辺を変更しない。
使われ方：指定した最終頂点の持ち上げ条件。 -/
lemma coneTipRestriction_edgeUnderCocone_val {K C : SSet.{u}} {q : K ⟶ C}
    {w z : JoinCocone q} (k : (sliceUnder q).Edge w z)
    (p : (Δ[0] : SSet.{u}) ⟶ C) (h : joinInr K Δ[0] ≫ w.val = p) :
    ((coneTipRestriction w p h).app (Opposite.op ⦋0⦌) (edgeUnderCocone k)).val =
      (edgeCosliceVertex (k.map (sliceUnderProjection q)).toTruncated).val := by
  change ((eqToIso (congrArg sliceUnder h)).hom.app (Opposite.op ⦋0⦌)
    ((sliceUnderRestrict w.val (joinInr K Δ[0])).app (Opposite.op ⦋0⦌)
      (edgeUnderCocone k))).val = _
  rw [Ind.sliceUnder_eqToIso_val h]
  exact edgeUnderCocone_tip k

/-- 概要：一段の因子化と元の一点下の表示から、元の入力図式の下の表示が存在する。
方針：元の比較辺を指定終点として全一点下表示を持ち上げ、余錐を忘却する。
規約：元の全入力と最終余錐を厳密に回収する。
使われ方：compact 成分生成表示の入力付き正規化。 -/
lemma exists_normalizedSourcePresentation_of_pointSource
    {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    {K C : SSet.{u + 1}} [Quasicategory C] {q : K ⟶ C}
    {w z : JoinCocone q} (k : (sliceUnder q).Edge w z)
    (p : (Δ[0] : SSet.{u + 1}) ⟶ C) (h : joinInr K Δ[0] ≫ w.val = p)
    {I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceUnder p)
    (c : JoinCocone D) (hc : IsColimitCone c)
    (ht : c.vertex.val = (edgeCosliceVertex (k.map (sliceUnderProjection q)).toTruncated).val) :
    ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ sliceUnder q,
      F ≫ sliceUnderProjection q = D ≫ sliceUnderProjection p ∧
      ∃ c' : JoinCocone F, IsColimitCone c' ∧ c'.vertex = z ∧
        c'.val ≫ sliceUnderProjection q = c.val ≫ sliceUnderProjection p := by
  have := coneTipRestriction_trivialKanFibration w p h
  have ht' : (coneTipRestriction w p h).app (Opposite.op ⦋0⦌)
      (edgeUnderCocone k) = c.vertex := by
    apply Subtype.ext
    exact (coneTipRestriction_edgeUnderCocone_val k p h).trans ht.symm
  obtain ⟨F, hF, c', hc', hv, haug⟩ := exists_normalizedSourcePresentation hμ w
    (coneTipRestriction w p h) (sliceUnderProjection p)
    (coneTipRestriction_projection w p h) D c hc (edgeUnderCocone k) ht'
  refine ⟨F, hF, c', hc', hv.trans ?_, haug⟩
  apply Subtype.ext
  rw [coneSourceForget_val]
  exact edgeUnderCocone_old k

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
