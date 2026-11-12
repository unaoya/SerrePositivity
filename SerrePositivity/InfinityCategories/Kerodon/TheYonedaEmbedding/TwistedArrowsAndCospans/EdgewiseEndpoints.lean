module

public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.EdgewiseSubdivision
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：edgewise subdivision から元の単体集合とその反転への自然な両端射影。
方針：join の左右の包含で制限し、標準単体の反転同型と Yoneda の同値を使う。
規約：二つの射影は任意の単体集合に対して定義し、同値性は別に証明する。
使われ方：Kerodon Notation 8.1.1.6（Tag 03JK）、Corollary 5.6.0.6（Tag 028T）、Kan 値図式の反転比較。

対応節は Kerodon 8.1（Tag 03JB）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans

/-- 概要：標準単体の反転同型の逆は単体圏の射を反転して移す。
方針：Yoneda の同値で各頂点を比較し、有限順序の二重反転を消去する。
規約：α は任意の面・退化とそれらの合成。
使われ方：Kerodon Notation 8.1.1.6（Tag 03JK）、左端射影の単体的自然性。 -/
lemma edgewiseStdSimplex_opIso_inv_naturality {a b : SimplexCategory} (α : a ⟶ b) :
    (stdSimplex.opIso.{u} a).inv ≫
        SSet.opFunctor.map (stdSimplex.map (SimplexCategory.rev.map α)) =
      stdSimplex.map α ≫ (stdSimplex.opIso b).inv := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  apply SSet.yonedaEquiv.injective
  apply SSet.opObjEquiv.injective
  apply stdSimplex.ext
  intro i
  change (α.toOrderHom i.rev.rev.rev).rev = (α.toOrderHom i.rev).rev
  rw [Fin.rev_rev]

/-- 概要：edgewise subdivision の右半分への制限は元の単体集合への射を与える。
方針：右包含で制限した標準単体を Yoneda の同値で単体に戻す。
規約：頂点では辺の終点を取る。
使われ方：Kerodon Notation 8.1.1.6（Tag 03JK）、自然な反転比較の右の射影。 -/
@[kerodon 03JK]
def edgewiseRight (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X ⟶ X where
  app n := ↾fun f ↦ SSet.yonedaEquiv
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (stdSimplex.obj n.unop).op (stdSimplex.obj n.unop) ≫ f)
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro f
    change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map α.unop ≫ f) =
      X.map α (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr _ _ ≫ f))
    erw [SSet.yonedaEquiv_naturality α.unop]
    congr 1

/-- 概要：edgewise subdivision の左半分への制限は元の単体集合の反転への射を与える。
方針：左包含で制限し、標準単体の反転同型で戻した単体を反転側の単体として読む。
規約：頂点では辺の始点を取る。
使われ方：Kerodon Notation 8.1.1.6（Tag 03JK）、自然な反転比較の左の射影。 -/
@[kerodon 03JK]
def edgewiseLeft (X : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivision X ⟶ X.op where
  app n := ↾fun f ↦ SSet.opObjEquiv.symm (SSet.yonedaEquiv
    ((stdSimplex.opIso n.unop).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (stdSimplex.obj n.unop).op (stdSimplex.obj n.unop) ≫ f))
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro f
    apply SSet.opObjEquiv.injective
    change SSet.yonedaEquiv ((stdSimplex.opIso m.unop).inv ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseWeight.map α.unop ≫ f) =
      X.map (SimplexCategory.rev.map α.unop).op (SSet.yonedaEquiv
        ((stdSimplex.opIso n.unop).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫ f))
    rw [SSet.yonedaEquiv_naturality]
    congr 1
    change (stdSimplex.opIso m.unop).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl _ _ ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.opFunctor.map (stdSimplex.map α.unop)) (stdSimplex.map α.unop) ≫ f = _
    have h := edgewiseStdSimplex_opIso_inv_naturality.{u} (SimplexCategory.rev.map α.unop)
    rw [SimplexCategory.rev_map_rev_map] at h
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap_assoc, ← Category.assoc]
    erw [h]
    rw [Category.assoc]
    rfl

/-- 概要：右端射影は単体集合の射について自然。
方針：重みからの射の後合成と右半分への制限の結合性を使う。
規約：X と Y の Kan 性は不要。
使われ方：Kerodon Remark 8.1.1.4（Tag 00B3）、Kan 値図式の右射影。 -/
lemma edgewiseRight_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f ≫ edgewiseRight Y = edgewiseRight X ≫ f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  rfl

/-- 概要：左端射影は単体集合の射とその反転について自然。
方針：重みからの射の後合成と左半分への制限の結合性を使う。
規約：反転は射にも同時に施す。
使われ方：Kerodon Remark 8.1.1.4（Tag 00B3）、Kan 値図式の左射影。 -/
lemma edgewiseLeft_naturality {X Y : SSet.{u}} (f : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.edgewiseSubdivisionMap f ≫ edgewiseLeft Y = edgewiseLeft X ≫ SSet.opFunctor.map f := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro g
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
