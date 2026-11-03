module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.EdgewiseRefinementImageIso

/-!
概要：元の二自然性正方形を同型の等式にし、同じ実共通終点の指定成分を消去する。
方針：元の辺の類の同型を使い、右正方形を左正方形へ代入する。
規約：指定比較の両定値成分と元の四つの辺の類を保持する。
使われ方：元の反転精密化と右精密化の作用を同じ全族で照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {X : SSet.{u}} {Y : SSet.{max u v}} [Quasicategory Y]
  [KanComplex ((SSet.uliftFunctor.{v, u}).obj (edgewiseSubdivision X))]
  {f g : (SSet.uliftFunctor.{v, u}).obj (edgewiseSubdivision X) ⟶ Y}
  (η : FunctorIso f g) (e : X _⦋1⦌)
local notation "T" => FunctorIso.app η (ULift.up (edgewiseRefinementVertex e))
local notation "S₀" => FunctorIso.app η (ULift.up (edgewiseRefinementVertex
  (CategoryTheory.Functor.map X (Quiver.Hom.op (SimplexCategory.const ⦋1⦌ ⦋1⦌ 0)) e)))
local notation "S₁" => FunctorIso.app η (ULift.up (edgewiseRefinementVertex
  (CategoryTheory.Functor.map X (Quiver.Hom.op (SimplexCategory.const ⦋1⦌ ⦋1⦌ 1)) e)))

/-- 元の右自然性正方形は、同じ実辺の類と同じ指定成分の同型の等式。 -/
lemma edgewiseRefinementRight_isoSquare :
    edgewiseRefinementRightImageIso f e ≪≫ T =
      S₀ ≪≫ edgewiseRefinementRightImageIso g e := by
  apply Iso.ext
  exact edgewiseRefinementRight_naturality η e

/-- 元の左自然性正方形も同じ実共通終点の成分を保持する同型の等式。 -/
lemma edgewiseRefinementLeft_isoSquare :
    edgewiseRefinementLeftImageIso f e ≪≫ T =
      S₁ ≪≫ edgewiseRefinementLeftImageIso g e := by
  apply Iso.ext
  exact edgewiseRefinementLeft_naturality η e

/-- 二正方形の同じ共通終点の成分を消去しても、四つの元の実辺の類を保持する。 -/
lemma edgewiseRefinement_common_component_cancel :
    edgewiseRefinementLeftImageIso f e ≪≫
        (edgewiseRefinementRightImageIso f e).symm ≪≫ S₀ ≪≫
          edgewiseRefinementRightImageIso g e =
      S₁ ≪≫ edgewiseRefinementLeftImageIso g e := by
  calc
    _ = edgewiseRefinementLeftImageIso f e ≪≫
        ((edgewiseRefinementRightImageIso f e).symm ≪≫
          (S₀ ≪≫ edgewiseRefinementRightImageIso g e)) := by
      simp only [Iso.trans_assoc]
    _ = edgewiseRefinementLeftImageIso f e ≪≫
        ((edgewiseRefinementRightImageIso f e).symm ≪≫
          (edgewiseRefinementRightImageIso f e ≪≫ T)) := by
      rw [← edgewiseRefinementRight_isoSquare η e]
    _ = edgewiseRefinementLeftImageIso f e ≪≫ T := by
      simp only [← Iso.trans_assoc, Iso.symm_self_id, Iso.refl_trans]
    _ = _ := edgewiseRefinementLeft_isoSquare η e

end SerrePositivity.InfinityCategories.F2
