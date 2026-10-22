module

public import SerrePositivity.InfinityCategories.F2.PointedRightFamilyTransportEndpoints
public import SerrePositivity.InfinityCategories.F2.FunctorIsoReverseHEq

/-!
概要：元の動く点・射の全比較を、同じ元の合成四角形の指定比較へ値まで戻す。
方針：既存の端点表示変更だけを外し、同じ実両端の式で逆同型を戻す。
規約：比較を選び直さない。使われ方：全右 Hom 比較の係数自然性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {K L : KanObject.{u}} {P : SSet.{u + 1}}
  (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L))
local notation "c" => x ≫ CategoryTheory.Functor.map SSet.uliftFunctor
  (Iso.inv (pointFunctorEvaluationIso (KanObject.obj K)))
local notation "D" => coherentKanRightCompositionTransport_diagonalIso pointKanObject K L
  pointedSpaceIdentityPoint c y

/-- 元の全右 Hom 比較の逆は、同じ元の合成四角形の全係数比較の指定値を保持する。 -/
lemma pointedRightFamilyTransportIso_symm_heq_diagonal :
    HEq (pointedRightFamilyTransportIso x y).symm D := by
  have hcast {α β : Sort (u + 2)} (h : α = β) (e : α) : HEq (Eq.mp h e) e := by
    cases h
    rfl
  unfold pointedRightFamilyTransportIso
  dsimp only
  rw [Iso.symm_symm_eq]
  exact (hcast _ _).trans ((hcast _ _).trans ((hcast _ _).trans (hcast _ _)))

/-- 元の全右 Hom 比較は、同じ元の合成四角形の比較の指定逆同型そのもの。 -/
lemma pointedRightFamilyTransportIso_heq_diagonal_symm :
    HEq (pointedRightFamilyTransportIso x y) (Iso.symm D) := by
  exact functorIso_heq_symm_of_symm_heq D (pointedRightFamilyTransportIso x y)
    (pointedRightFamilyTransport_diagonal_source x y)
    (pointedRightFamilyTransport_diagonal_target x y)
    (pointedRightFamilyTransportIso_symm_heq_diagonal x y)

end SerrePositivity.InfinityCategories.F2
