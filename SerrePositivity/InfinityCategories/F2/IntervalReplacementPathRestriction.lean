module

public import SerrePositivity.InfinityCategories.F2.IntervalPullbackPathIsoComparison
public import SerrePositivity.InfinityCategories.F2.IntervalPathPrecompCylinder
public import SerrePositivity.InfinityCategories.F2.HomotopyIsoRawComparison
public import SerrePositivity.InfinityCategories.F2.HomotopyIsoWhiskering

/-!
概要：区間置換と引き戻しの指定 path を、元の比較射に沿って同じ指定類として比較する。
方針：全円柱を uncurry の自然性で一致させ、両端評価を保持する型付き比較を使う。
規約：指定類を保持。使われ方：共通の引き戻しの左脚の底の像の正規化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {A X Y Z : SSet.{u}} [KanComplex Z] (f : X ⟶ Z) (g : Y ⟶ Z)

/-- 第一置換の元の path の制限と、引き戻しの元の path の制限は同じ指定類である。 -/
lemma intervalReplacementPathIso_precomp_heq_pullback (a : A ⟶ intervalPullback f g) :
    HEq ((intervalReplacementPathIso f).precomp
      (a ≫ pullback.fst (intervalReplacementEndpoint f) g))
      ((intervalPullbackPathIso f g).precomp a) := by
  have he : intervalReplacementPathIso f =
      functorIsoOfSimplicialHomotopy (intervalReplacementCanonicalPathHomotopy f) := by
    apply Iso.ext
    rfl
  have hd : intervalPullbackPathIso f g =
      functorIsoOfSimplicialHomotopy (intervalPullbackPathHomotopy f g) := by
    apply Iso.ext
    rfl
  rw [he, hd, ← homotopyIso_precomp, ← homotopyIso_precomp]
  apply homotopyIso_heq_of_h_eq
  apply SSet.hom_ext
  intro n
  rfl

/-- 指定円柱から作った元の引き戻し点の path は、同じ円柱の指定類を回収する。 -/
lemma intervalPullbackHomotopyPoint_pathIso_heq (a : A ⟶ X) (b : A ⟶ Y)
    (H : SSet.Homotopy (a ≫ f) (b ≫ g)) :
    HEq ((intervalPullbackPathIso f g).precomp (intervalPullbackHomotopyPoint f g a b H))
      (functorIsoOfSimplicialHomotopy H) := by
  have he : intervalPullbackPathIso f g =
      functorIsoOfSimplicialHomotopy (intervalPullbackPathHomotopy f g) := by
    apply Iso.ext
    rfl
  rw [he, ← homotopyIso_precomp]
  apply homotopyIso_heq_of_h_eq
  rw [intervalPullbackPathHomotopy_precomp_cylinder,
    intervalPullbackHomotopyPoint_path, uncurry_curry, ← Category.assoc,
    SymmetricCategory.symmetry]
  rfl

end SerrePositivity.InfinityCategories.F2
