module

public import SerrePositivity.KST.Spectra.PointedVerticalChains

/-!
概要：元の成分から基点固定区間を選び、前後の合成で区間全体の式を保持する。
方針：点への射影を持つ VerticalPath を用い、元の内部 Hom の評価の自然性を計算する。
規約：一般の指定部分への垂直性は主張しない。使われ方：交換符号の普遍的な区間族。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
namespace SerrePositivity.KST.Spectra.PointedMapping

/-- 同じ成分の二つの点つき射を、元の内部 Hom の基点固定区間で結ぶ。 -/
def basedPathOfComponent {A E : PointedSimplicialSet.{u}} [KanComplex E.right]
    {f g : A ⟶ E} (h : componentOf f = componentOf g) :
    VerticalPath (PointedObject.toPoint E) f g := by
  let hex := (piZero_eq_iff_pointedHomotopy f g).1 h
  exact VerticalPath.ofHomotopy hex.choose hex.choose_spec (toUnit_unique _ _)

namespace VerticalPath
variable {A E B : PointedSimplicialSet.{u}} {p : E ⟶ B} {f g : A ⟶ E}

/-- 厳密に等しい端点の表示へ移しても、元の区間族そのものを保持する。 -/
def changeEndpoints (H : VerticalPath p f g) {f' g' : A ⟶ E}
    (hf : f' = f) (hg : g' = g) : VerticalPath p f' g' where
  path := H.path
  zero := by rw [hf]; exact H.zero
  one := by rw [hg]; exact H.one
  «over» := by rw [hf]; exact H.over

/-- 端点の厳密な表示の変更は、元のホモトピーの区間全体の射を変更しない。 -/
lemma changeEndpoints_homotopy_h (H : VerticalPath p f g) {f' g' : A ⟶ E}
    (hf : f' = f) (hg : g' = g) :
    (H.changeEndpoints hf hg).homotopy.h = H.homotopy.h := by
  rw [homotopy_h, homotopy_h]
  rfl

/-- 前合成で移した区間の実際のホモトピーは、元の区間全体への同じ前合成。 -/
lemma pre_homotopy_h (H : VerticalPath p f g) {T : PointedSimplicialSet.{u}} (i : T ⟶ A) :
    (H.pre i).homotopy.h = i.right ▷ (Δ[1] : SSet.{u}) ≫ H.homotopy.h := by
  rw [homotopy_h, homotopy_h]
  change uncurry ((H.path ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i E) ≫ PointedObject.basedHomι T E) = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc, uncurry_pre_app]

/-- 後合成で移した区間の実際のホモトピーは、元の区間全体への同じ後合成。 -/
lemma post_homotopy_h (H : VerticalPath p f g) {E' B' : PointedSimplicialSet.{u}}
    (q : E' ⟶ B') (v : E ⟶ E') (w : B ⟶ B') (h : v ≫ q = p ≫ w) :
    (H.post q v w h).homotopy.h = H.homotopy.h ≫ v.right := by
  rw [homotopy_h, homotopy_h]
  change uncurry ((H.path ≫ (PointedObject.basedHomMap A v).right) ≫
    PointedObject.basedHomι A E') = _
  rw [Category.assoc, PointedObject.basedHomMap_ι, ← Category.assoc, uncurry_natural_right]

/-- 基点固定区間の後合成。元の同じ区間族を使う。 -/
def basedPost {A E E' : PointedSimplicialSet.{u}} {f g : A ⟶ E}
    (H : VerticalPath (PointedObject.toPoint E) f g) (v : E ⟶ E') :
    VerticalPath (PointedObject.toPoint E') (f ≫ v) (g ≫ v) :=
  H.post (PointedObject.toPoint E') v (𝟙 PointedObject.point)
    (PointedObject.point_isZero.eq_of_tgt _ _)

/-- 基点固定区間の後合成も、元の区間全体への同じ後合成。 -/
lemma basedPost_homotopy_h {A E E' : PointedSimplicialSet.{u}} {f g : A ⟶ E}
    (H : VerticalPath (PointedObject.toPoint E) f g) (v : E ⟶ E') :
    (H.basedPost v).homotopy.h = H.homotopy.h ≫ v.right := post_homotopy_h ..

end VerticalPath

namespace VerticalChain

/-- 基点固定区間の有限鎖を、元の後合成で移す。 -/
lemma basedPost {A E E' : PointedSimplicialSet.{u}} {f g : A ⟶ E}
    (H : VerticalChain (PointedObject.toPoint E) f g) (v : E ⟶ E') :
    VerticalChain (PointedObject.toPoint E') (f ≫ v) (g ≫ v) :=
  H.post (PointedObject.toPoint E') v (𝟙 PointedObject.point)
    (PointedObject.point_isZero.eq_of_tgt _ _)

/-- loop 値の基点固定区間の有限鎖を、元の評価で uncurry する。 -/
lemma basedUncurry {A V : PointedSimplicialSet.{u}} {f g : A ⟶ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace V}
    (H : VerticalChain (PointedObject.toPoint (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace V)) f g) :
    VerticalChain (PointedObject.toPoint V) (uncurry f) (uncurry g) := by
  have hs := H.suspension.post (PointedObject.toPoint V)
    ((ihom.ev PointedSimplicialSet.circle.{u}).app V)
    (PointedObject.toPoint (PointedSimplicialSet.circle.{u} ⊗ PointedObject.point))
    (PointedObject.point_isZero.eq_of_tgt _ _)
  exact hs

end VerticalChain
end SerrePositivity.KST.Spectra.PointedMapping
