module

public import SerrePositivity.KST.Spectra.PointedIntervalProjectedNaturality

/-!
概要：元の実自然性正方形に入力制限と射影を作用させ、元の射影付き二辺へ戻す。
方針：同じ二次元射へ内部 Hom の前後合成を作用させ、厳密な射影可換式で照合する。
規約：四辺を選び直さない。使われ方：交換符号辺の実入力に沿う自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.KST.Spectra.PointedMapping.VerticalPath

/-- 厳密な射影可換式は、元の二重後合成を同じ入力制限付きの辺へ照合する。 -/
lemma projectedPost_path {A D D' E E' : PointedSimplicialSet.{u}}
    {f g : D ⟶ D} (P : VerticalPath (PointedObject.toPoint D) f g)
    (i : A ⟶ D) (v : D ⟶ D') (q : D ⟶ E) (q' : D' ⟶ E') (w : E ⟶ E')
    (hq : q ≫ w = v ≫ q') :
    (((P.pre i).basedPost q).basedPost w).path =
      (((P.basedPost v).pre i).basedPost q').path := by
  rw [basedPost_basedPost_path, hq, ← basedPost_basedPost_path]
  exact congrArg (· ≫ (PointedObject.basedHomMap A q').right) (P.pre_basedPost_path i v).symm

/-- 同じ正方形への入力制限・射影は、元の射影付き二辺の実自然性正方形を与える。 -/
def projectedNaturalitySquare {A D D' E E' : PointedSimplicialSet.{u}}
    {f g : D ⟶ D} {f' g' : D' ⟶ D'}
    (P : VerticalPath (PointedObject.toPoint D) f g)
    (Q : VerticalPath (PointedObject.toPoint D') f' g')
    (i : A ⟶ D) (v : D ⟶ D') (q : D ⟶ E) (q' : D' ⟶ E') (w : E ⟶ E')
    (hq : q ≫ w = v ≫ q')
    (H : SSet.Homotopy (P.basedPost v).path (Q.pre v).path) :
    SSet.Homotopy (((P.pre i).basedPost q).basedPost w).path
      ((Q.pre (i ≫ v)).basedPost q').path where
  h := H.h ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i D').right ≫ (PointedObject.basedHomMap A q').right
  h₀ := by
    rw [← Category.assoc, ← Category.assoc, H.h₀]
    exact (projectedPost_path P i v q q' w hq).symm
  h₁ := by
    rw [← Category.assoc, ← Category.assoc, H.h₁]
    exact congrArg (· ≫ (PointedObject.basedHomMap A q').right) (Q.pre_pre_path v i)
  rel := by ext m ⟨⟨s, hs⟩, t⟩; exact hs.elim

end SerrePositivity.KST.Spectra.PointedMapping.VerticalPath
