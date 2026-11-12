module

public import SerrePositivity.KST.Spectra.CancellationFirstNaturality
public import SerrePositivity.KST.Spectra.PointedIntervalInputBoundary

/-!
概要：入力制限・射影後の区間を、厳密な可換式と元の自然性の辺全体で照合する。
方針：前後合成の実辺の公式を用い、元の二つの区間を選び直さず比較する。
規約：自然性は実辺の等式として入力。使われ方：二重反転区間の実入力に沿う自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalPath

/-- 射影可換式を内部 Hom の入力制限と後合成の射全体へ移す。 -/
lemma projectedCoordinate {A D D' E E' : PointedSimplicialSet.{u}}
    (i : A ⟶ D) (v : D ⟶ D') (q : D ⟶ E) (q' : D' ⟶ E') (w : E ⟶ E')
    (hq : q ≫ w = v ≫ q') :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i D ≫ PointedObject.basedHomMap A q) ≫ PointedObject.basedHomMap A w =
      (PointedObject.basedHomMap D v ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i D') ≫ PointedObject.basedHomMap A q' := by
  have hn := (MonoidalClosed.pre i).naturality v
  simp only [← _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed_eq_closedPre] at hn
  change (ihom D).map v ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i D' = _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i D ≫ (ihom A).map v at hn
  change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i D ≫ (ihom A).map q) ≫ (ihom A).map w =
    ((ihom D).map v ≫ _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i D') ≫ (ihom A).map q'
  rw [Category.assoc, ← Functor.map_comp, hq, Functor.map_comp, ← Category.assoc, ← hn]

/-- 実辺の自然性と射影可換式から、入力制限・射影付き実辺の等式を得る。 -/
lemma projectedNaturality_map {T : SSet.{u}} {A D D' E E' : PointedSimplicialSet.{u}}
    (R : T ⟶ (PointedObject.basedHom D D).right)
    (R' : T ⟶ (PointedObject.basedHom D' D').right)
    (i : A ⟶ D) (v : D ⟶ D') (q : D ⟶ E) (q' : D' ⟶ E') (w : E ⟶ E')
    (hq : q ≫ w = v ≫ q')
    (hp : R ≫ (PointedObject.basedHomMap D v).right = R' ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed v D').right) :
    ((R ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i D).right) ≫ (PointedObject.basedHomMap A q).right) ≫
        (PointedObject.basedHomMap A w).right =
      (R' ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed (i ≫ v) D').right) ≫ (PointedObject.basedHomMap A q').right := by
  have hc := congrArg (fun m => R ≫ m.right) (projectedCoordinate i v q q' w hq)
  simp only [Under.comp_right, Category.assoc] at hc
  simp only [Category.assoc]
  rw [hc, ← Category.assoc R, hp]
  have ht := congrArg (fun m => R' ≫ m.right ≫ (PointedObject.basedHomMap A q').right)
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.PointedMapping.prePointed_comp i v D')
  simpa only [Under.comp_right, Category.assoc] using ht

/-- 入力制限と射影を付けた元の区間全体を、同じ自然性の辺へ照合する。 -/
lemma projectedNaturality_path {A D D' E E' : PointedSimplicialSet.{u}}
    {f g : D ⟶ D} {f' g' : D' ⟶ D'}
    (P : VerticalPath (PointedObject.toPoint D) f g)
    (Q : VerticalPath (PointedObject.toPoint D') f' g')
    (i : A ⟶ D) (v : D ⟶ D') (q : D ⟶ E) (q' : D' ⟶ E') (w : E ⟶ E')
    (hq : q ≫ w = v ≫ q')
    (hp : (P.basedPost v).path = (Q.pre v).path) :
    (((P.pre i).basedPost q).basedPost w).path =
      ((Q.pre (i ≫ v)).basedPost q').path := by
  rw [basedPost_basedPost_path, hq, ← basedPost_basedPost_path]
  have he := congrArg (fun t =>
    (t ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i D').right) ≫ (PointedObject.basedHomMap A q').right) hp
  change (((P.basedPost v).pre i).basedPost q').path =
    (((Q.pre v).pre i).basedPost q').path at he
  have hleft := congrArg (· ≫ (PointedObject.basedHomMap A q').right)
    (P.pre_basedPost_path i v)
  have hright := congrArg (· ≫ (PointedObject.basedHomMap A q').right) (Q.pre_pre_path v i)
  exact hleft.symm.trans (he.trans hright)

end SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
