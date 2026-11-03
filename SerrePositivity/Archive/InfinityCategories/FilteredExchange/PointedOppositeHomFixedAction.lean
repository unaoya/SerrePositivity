module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedOppositeHomAction
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.OppositeHomFixedPostcomposition

/-!
概要：全反転 Hom の作用族を固定 Kan 射で制限すると元の後合成作用そのもの。
方針：反転係数の全退化を豊穣後合成の反転へ戻し、同じ全円柱を計算する。
規約：全係数・元の標準 fiber 比較・元の固定射を保持する。
使われ方：指定同型の両端を元の実二辺合成・長辺の関手として正規化する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K L : KanObject.{u}}

/-- 固定した元の Kan 射の係数への制限は、全初点に対する同じ後合成作用。 -/
lemma pointedOppositeHomAction_fixed_uncurry {P : SSet.{u + 1}} (f : K ⟶ L) :
    uncurry ((SSet.const (ULift.up (SSet.opObjEquiv.symm
      (SimplicialCategory.homEquiv' K L f))) : P ⟶ _) ≫ pointedOppositeHomAction K L) =
    fst ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom pointKanObject K).op) P ≫
      (SSet.uliftFunctor.{u + 1, u}).map
        (SSet.opFunctor.map (eHomWhiskerLeft SSet pointKanObject f)) ≫
          pointedCoherentFiberComparison L := by
  let A := (SSet.uliftFunctor.{u + 1, u}).obj
    (SimplicialCategory.sHom pointKanObject K).op
  let H := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L).op
  let c : H.obj (Opposite.op (SimplexCategory.mk 0)) :=
    ULift.up (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' K L f))
  have hp : lift (snd A P ≫ (SSet.const c : P ⟶ H)) (fst A P) =
      fst A P ≫ lift (SSet.const c : A ⟶ H) (𝟙 A) := by
    simp only [comp_lift, SSet.comp_const, Category.comp_id]
  have hu : lift (SSet.const c) (𝟙 A) ≫
      (uliftTensorIso (SimplicialCategory.sHom K L).op
        (SimplicialCategory.sHom pointKanObject K).op).inv =
      (SSet.uliftFunctor.{u + 1, u}).map
        (lift (SSet.const (SSet.opObjEquiv.symm (SimplicialCategory.homEquiv' K L f)))
          (𝟙 (SimplicialCategory.sHom pointKanObject K).op)) := rfl
  rw [pointedOppositeHomAction_uncurry]
  change lift (snd A P ≫ SSet.const c) (fst A P) ≫ _ = _
  rw [hp, ← Category.assoc, ← Category.assoc, Category.assoc (fst A P), hu]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, oppositeHomPrecomposition_fixed]

end SerrePositivity.InfinityCategories.F2
