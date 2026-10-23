module

public import SerrePositivity.InfinityCategories.F1.FunctorCategories.FunctorIsoEdgeRepresentative
public import SerrePositivity.InfinityCategories.F1.Pullbacks.PullbackCompatibleEdgeHomotopy

/-!
概要：共有頂点への指定像が一致する成分同型を、同じ pullback 上の関手同型へ束ねる。
方針：左の代表辺の像を右の元の代表辺へ両端固定で揃え、円柱を貼り合わせる。
規約：パラメーターは任意。元の二射と成分同型の類を保持する。
使われ方：元の分類 Hom 作用と補正 pullback 比較の同型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 元の pullback への同じ射の二射影は、底への合成で一致する。 -/
lemma pullbackProjectionComposite_eq {A X Y Z : SSet.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (a : A ⟶ pullback f g) :
    (a ≫ pullback.fst f g) ≫ f = (a ≫ pullback.snd f g) ≫ g :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun m ↦ a ≫ m) (pullback.condition (f := f) (g := g))).trans
      (Category.assoc _ _ _).symm)

/-- 指定像が一致する成分同型は、元の二射を結ぶ pullback の関手同型を与える。 -/
def pullbackFunctorIsoOfCompatibleIsos {A X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    (f : X ⟶ Z) (g : Y ⟶ Z) [LeftFibration f] [KanComplex (pullback f g)]
    (a b : A ⟶ pullback f g)
    (L : FunctorIso (a ≫ pullback.fst f g) (b ≫ pullback.fst f g))
    (R : FunctorIso (a ≫ pullback.snd f g) (b ≫ pullback.snd f g))
    (h : F2.functorIsoOfEq (L.postcomp f)
      (pullbackProjectionComposite_eq f g a) (pullbackProjectionComposite_eq f g b) =
      R.postcomp g) : FunctorIso a b := Classical.choice (by
  let r := (FunctorIso.edge R).map ((truncation 2).map ((ihom A).map g))
  have hr : SSet.Truncated.HomotopyCategory.homMk r = (R.postcomp g).hom := by
    rw [F2.functorIso_postcomp_hom, ← FunctorIso.edge_homMk R]
    rfl
  obtain ⟨l, hl, _⟩ := functorIso_exists_edge_representative_over f L (R.postcomp g)
    (pullbackProjectionComposite_eq f g a) (pullbackProjectionComposite_eq f g b) h r hr
  exact ⟨functorIsoOfSimplicialHomotopy
    (pullbackHomotopyOfCompatibleEdges f g a b l (FunctorIso.edge R) hl)⟩)

end SerrePositivity.InfinityCategories
