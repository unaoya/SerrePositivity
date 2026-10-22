module
public import SerrePositivity.InfinityCategories.Derived.FunctorIsoInverseSourceComparison
/-!
概要：元の一般合成子を最初の比較と残りの比較へ厳密に分解する。
方針：同じ比較値・前後合成の交換則を保持する。
規約：同値の三角式は仮定しない。使われ方：一般 cell 合成子の五角式。
-/
@[expose] public section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
def functorIsoSandwichTail {A B Y C Z : SSet.{u}}
    (h : B ⟶ Y) (i : Y ⟶ B) (t : C ⟶ Z) (e : FunctorIso (h ≫ i) (𝟙 B))
    (G : Y ⟶ Z) (M : A ⟶ B) (N : B ⟶ C) (T : A ⟶ C)
    (b : FunctorIso G (i ≫ N ≫ t)) (k : FunctorIso (M ≫ N) T) :
    FunctorIso (M ≫ h ≫ G) (T ≫ t) := by
  have d : FunctorIso ((M ≫ h) ≫ (i ≫ N ≫ t)) (M ≫ N ≫ t) := by
    have q := (e.postcomp (N ≫ t)).precomp M
    exact q
  have c : FunctorIso (M ≫ N ≫ t) (T ≫ t) := by
    have q := k.postcomp t
    exact q
  exact b.precomp (M ≫ h) ≪≫ d ≪≫ c
lemma functorIsoSandwichCompositor_tail {X A B Y C Z : SSet.{u}}
    (s : X ⟶ A) (h : B ⟶ Y) (i : Y ⟶ B) (t : C ⟶ Z)
    (e : FunctorIso (h ≫ i) (𝟙 B))
    (F : X ⟶ Y) (G : Y ⟶ Z) (M : A ⟶ B) (N : B ⟶ C) (T : A ⟶ C)
    (a : FunctorIso F (s ≫ M ≫ h)) (b : FunctorIso G (i ≫ N ≫ t))
    (k : FunctorIso (M ≫ N) T) :
    functorIsoSandwichCompositor s h i t e F G M N T a b k =
      a.postcomp G ≪≫ (functorIsoSandwichTail h i t e G M N T b k).precomp s := by
  simp only [functorIsoSandwichCompositor, functorIsoSandwichTail,
    F2.functorIso_precomp_trans, F2.functorIso_precomp_precomp, Iso.trans_assoc]
  rfl
end
end SerrePositivity.InfinityCategories
