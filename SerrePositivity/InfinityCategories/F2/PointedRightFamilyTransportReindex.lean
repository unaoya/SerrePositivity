module

public import SerrePositivity.InfinityCategories.F2.PointedRightFamilyTransportPresentation
public import SerrePositivity.InfinityCategories.F2.CoherentRightCompositionDiagonalReindex

/-!
概要：元の動く点・射の全右 Hom 比較は、任意の全係数制限でも指定値を保持する。
方針：同じ合成四角形の指定比較へ戻し、全二 Hom 比較の係数自然性を適用する。
規約：点・射・比較を選び直さない。使われ方：全族の単位・余単位の因子の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {K L : KanObject.{u}} {P Q : SSet.{u + 1}}
  (x : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj K.obj)
  (y : P ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom K L)) (r : Q ⟶ P)
local notation "c" => x ≫ CategoryTheory.Functor.map SSet.uliftFunctor
  (Iso.inv (pointFunctorEvaluationIso (KanObject.obj K)))
local notation "D" => coherentKanRightCompositionTransport_diagonalIso pointKanObject K L
  pointedSpaceIdentityPoint c y
local notation "Dᵣ" => coherentKanRightCompositionTransport_diagonalIso pointKanObject K L
  pointedSpaceIdentityPoint (r ≫ c) (r ≫ y)

/-- 元の動く点・射の全比較は、全係数の二段制限でも値まで同じ指定比較となる。 -/
lemma pointedRightFamilyTransportIso_precomp_heq :
    HEq ((pointedRightFamilyTransportIso x y).precomp r)
      (pointedRightFamilyTransportIso (r ≫ x) (r ≫ y)) := by
  have h := functorIso_precomp_heq_of_heq (Iso.symm D) (pointedRightFamilyTransportIso x y)
    (pointedRightFamilyTransport_diagonal_target x y)
    (pointedRightFamilyTransport_diagonal_source x y)
    (pointedRightFamilyTransportIso_heq_diagonal_symm x y) r
  have hd := coherentKanRightCompositionTransport_diagonalIso_precomp_heq
    pointKanObject K L pointedSpaceIdentityPoint c y r
  have hs := functorIso_symm_heq_of_heq (FunctorIso.precomp D r) Dᵣ
    (by simp only [diagonalFiberTransport_precomp, SSet.comp_const, ← Category.assoc])
    (by simp only [diagonalFiberTransport_precomp, SSet.comp_const, ← Category.assoc, comp_lift])
    hd.symm
  exact h.trans ((heq_of_eq (functorIso_precomp_symm D r)).trans
    (hs.symm.trans (pointedRightFamilyTransportIso_heq_diagonal_symm
      (r ≫ x) (r ≫ y)).symm))

end SerrePositivity.InfinityCategories.F2
