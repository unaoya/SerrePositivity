module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.PointedRightFamilyTransportReindex

/-!
概要：元の任意の全右 Hom 比較を、同じ全直積上の一つの指定比較の制限で表す。
方針：元の全比較の係数自然性を、動く点と動く射の組に適用する。
規約：全直積と指定値を保持。使われ方：単位・余単位の成分と同じ全族の自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {K L : KanObject.{u}} {P : SSet.{u + 1}}
  (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor (KanObject.obj K)
local notation "H" => CategoryTheory.Functor.obj SSet.uliftFunctor (SimplicialCategory.sHom K L)
local notation "U" => pointedRightFamilyTransportIso (fst A H) (snd A H)

/-- 元の全右 Hom 比較は、全直積上の同じ一つの指定比較の前合成そのもの。 -/
lemma pointedRightFamilyTransportIso_heq_universal :
    HEq (pointedRightFamilyTransportIso x y) (FunctorIso.precomp U (lift x y)) := by
  have h := pointedRightFamilyTransportIso_precomp_heq (fst A H) (snd A H) (lift x y)
  have hx : lift x y ≫ fst A H = x := CartesianMonoidalCategory.lift_fst x y
  have hy : lift x y ≫ snd A H = y := CartesianMonoidalCategory.lift_snd x y
  rw [hx, hy] at h
  exact h.symm

end SerrePositivity.InfinityCategories.F2
