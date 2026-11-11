module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentColimitCoconeHomotopy
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle

/-!
概要：元の指定三角形を、元の全空間余錐間の三角形へ持ち上げる。
方針：普遍余錐の切断で全二単体を写し、底と頂点の評価を照合する。
規約：三辺と全二単体を保持。使われ方：native 比較との全三角形の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  {l : SSet.Homotopy F G} {r : SSet.Homotopy G J} {d : SSet.Homotopy F J}
  (T : FunctorCompositionTriangle l r d)

/-- 元の全余錐と三辺を保持した、指定二単体の持ち上げ。 -/
def coherentColimitCoconeTriangle :
    FunctorCompositionTriangle (coherentColimitCoconeHomotopy B l)
      (coherentColimitCoconeHomotopy B r) (coherentColimitCoconeHomotopy B d) where
  diagram := T.diagram ≫ coherentColimitCoconeFunctor B
  face_zero := by
    rw [← Category.assoc, T.face_zero, coherentColimitCoconeHomotopy_curry]
  face_one := by
    rw [← Category.assoc, T.face_one, coherentColimitCoconeHomotopy_curry]
  face_two := by
    rw [← Category.assoc, T.face_two, coherentColimitCoconeHomotopy_curry]

/-- 元の図式への制限は、三辺だけでなく元の指定二単体全体を回収する。 -/
lemma coherentColimitCoconeTriangle_restrict :
    (coherentColimitCoconeTriangle B T).diagram ≫ coconeRestriction _ _ = T.diagram := by
  change (T.diagram ≫ coherentColimitCoconeFunctor B) ≫ _ = _
  rw [Category.assoc, coherentColimitCoconeFunctor_restrict, Category.comp_id]

/-- 全余錐の三角形の頂点評価は、余極限関手による元の全二単体の像。 -/
lemma coherentColimitCoconeTriangle_apex :
    (coherentColimitCoconeTriangle B T).diagram ≫ evaluateFunctorAt
      (SSet.yonedaEquiv (joinInr ((SSet.uliftFunctor.{u + 1, u}).obj B)
        (Δ[0] : SSet.{u + 1}))) = T.diagram ≫ coherentColimitFunctor B := by
  exact Category.assoc _ _ _

end SerrePositivity.InfinityCategories.F2
