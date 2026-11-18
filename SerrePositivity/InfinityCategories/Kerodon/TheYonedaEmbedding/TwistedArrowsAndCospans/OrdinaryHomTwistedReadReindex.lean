module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.OrdinaryHomTwistedRead

/-!
概要：twisted arrow から読み戻した Hom の元は全順序写像による再添字を保つ。
方針：既存の edgewise の左右の頂点の座標式を使い、同じ両端間の射を比較する。
規約：ここでは各対象の全族の一致を扱い、読み戻しの単位・余単位は後続とする。
使われ方：Kerodon Proposition 8.1.1.10（Tag 03JN）、HTT 5.1.5.6 の模型比較の単位則。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
variable {C : Type u} [SmallCategory C] {m n : ℕ}

private lemma elements_hext {A : Type u} [SmallCategory A] {F : A ⥤ Type u}
    (x y : F.Elements) (ho : x.obj = y.obj) (hv : HEq x.val y.val) : x = y := by
  cases x
  cases y
  cases ho
  cases (eq_of_heq hv)
  rfl

private lemma longMap_heq {r : ℕ} (L : ComposableArrows C r)
    {i j i' j' : Fin (r + 1)} (hi : i = i') (hj : j = j')
    (f : i ⟶ j) (g : i' ⟶ j') : HEq (L.map f) (L.map g) := by
  subst i' j'
  have hh : f = g := Subsingleton.elim _ _
  subst g
  rfl

/-- 長い射列から読んだ元は実際の edgewise 重みの全再添字で保たれる。
Kerodon Proposition 8.1.1.10（Tag 03JN）、読み戻しの各対象の自然性の法則。 -/
lemma ordinaryHomFromLongObj_reindex (L : ComposableArrows C (n + n + 1))
    (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    ordinaryHomFromLongObj ((edgewiseWeightReindexOrderHom.{u} α).toFunctor ⋙ L) i =
      ordinaryHomFromLongObj L (α.toOrderHom i) := by
  have hl := edgewiseWeightReindexOrderHom_left.{u} α i
  have hr := edgewiseWeightReindexOrderHom_right.{u} α i
  apply elements_hext
  · change (Opposite.op (L.obj (edgewiseWeightReindexOrderHom.{u} α (edgewiseLeftVertex m i))),
      L.obj (edgewiseWeightReindexOrderHom.{u} α (edgewiseRightVertex m i))) = _
    rw [hl, hr]
    rfl
  · change HEq (L.map (homOfLE _)) (L.map (homOfLE _))
    exact longMap_heq L hl hr _ _

/-- 実際の重みの再添字は、指定した長い射列の同じ再添字になる。
Kerodon Proposition 8.1.1.10（Tag 03JN）、標準単体模型の全再添字の法則。 -/
lemma edgewiseLongChain_reindex (f : (TwistedArrow (nerve C)) _⦋n⦌)
    (α : ⦋m⦌ ⟶ ⦋n⦌) :
    edgewiseSimplexEquiv (nerve C) m (edgewiseWeight.map α ≫ f) =
      (edgewiseWeightReindexOrderHom.{u} α).toFunctor ⋙
        edgewiseSimplexEquiv (nerve C) n f := by
  change SSet.yonedaEquiv ((edgewiseWeightIso m).inv ≫ edgewiseWeight.map α ≫ f) =
    (nerve C).map (SimplexCategory.mkHom (edgewiseWeightReindexOrderHom.{u} α)).op
      (SSet.yonedaEquiv ((edgewiseWeightIso n).inv ≫ f))
  rw [SSet.yonedaEquiv_naturality]
  have he : (edgewiseWeightIso.{u} m).inv ≫ edgewiseWeight.map α =
      stdSimplex.map (SimplexCategory.mkHom (edgewiseWeightReindexOrderHom.{u} α)) ≫
        (edgewiseWeightIso.{u} n).inv := by
    rw [edgewiseWeightReindexOrderHom_map, edgewiseWeightStandardMap]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, he, Category.assoc]

/-- 実際の twisted arrow の読み戻しの各対象は全順序写像に自然である。
Kerodon Proposition 8.1.1.10（Tag 03JN）、指定した各対角の射の族の自然性。 -/
lemma ordinaryHomTwistedRead_obj_reindex (f : (TwistedArrow (nerve C)) _⦋n⦌)
    (α : ⦋m⦌ ⟶ ⦋n⦌) (i : Fin (m + 1)) :
    (ordinaryHomTwistedRead (edgewiseWeight.map α ≫ f)).obj i =
      (ordinaryHomTwistedRead f).obj (α.toOrderHom i) := by
  change ordinaryHomFromLongObj (edgewiseSimplexEquiv (nerve C) m _) i = _
  rw [edgewiseLongChain_reindex]
  exact ordinaryHomFromLongObj_reindex _ α i

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
