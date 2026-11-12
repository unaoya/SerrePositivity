module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.LayerTriangles
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorEnrichment

/-!
概要：一対象環からの指定対象関手の族に、元の全 Hom 作用を与える。
方針：一つの変換成分を Hom end へ持ち上げ、単位と合成を評価で検査する。
規約：cell 分解や固定 ε への持ち上げは、この関手からは主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory MonoidalCategory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]

/-- 指定対象の間の全 Hom は、一対象入力では自然なパラメータを与える。 -/
def dgPointFamilyParameter (x y : D) :
    DGFunctorParamTrans R PUnit.{1} D (homObject R D x y)
      (DGQuotient.pointDGFunctor R D x) (DGQuotient.pointDGFunctor R D y) where
  app _ := 𝟙 _
  naturality _ _ := by
    have hl : (eId (Complex R) x ⊗ₘ 𝟙 (homObject R D x y)) ≫
        eComp (Complex R) x x y = (λ_ _).hom := by
      apply (cancel_epi (λ_ (homObject R D x y)).inv).mp
      simpa using e_id_comp (Complex R) x y
    have hr : (𝟙 (homObject R D x y) ⊗ₘ eId (Complex R) y) ≫
        eComp (Complex R) x y y = (ρ_ _).hom := by
      apply (cancel_epi (ρ_ (homObject R D x y)).inv).mp
      simpa using e_comp_id (Complex R) x y
    change (β_ (homObject R D x y) (𝟙_ (Complex R))).hom ≫
      (eId (Complex R) x ⊗ₘ 𝟙 _) ≫ eComp (Complex R) x x y =
      (𝟙 (homObject R D x y) ⊗ₘ eId (Complex R) y) ≫ eComp (Complex R) x y y
    rw [hl, hr]
    exact braiding_leftUnitor _

/-- Hom end に持つ同じ一成分パラメータ。 -/
def dgPointFamilyHom (x y : D) :
    homObject R D x y ⟶ dgFunctorHom R PUnit.{1} D
      (DGQuotient.pointDGFunctor R D x) (DGQuotient.pointDGFunctor R D y) :=
  (dgFunctorHomEquiv R PUnit.{1} D _ _ _).symm (dgPointFamilyParameter R D x y)

@[reassoc (attr := simp)]
lemma dgPointFamilyHom_π (x y : D) (a : PUnit.{1}) :
    dgPointFamilyHom R D x y ≫ dgFunctorHomπ R PUnit.{1} D _ _ a = 𝟙 _ :=
  dgFunctorHomEquiv_symm_π R PUnit.{1} D _ _ _ _ a

/-- 指定対象関手を対象・全 Hom にわたり構成する dg 関手。 -/
def dgPointFamily : DGFunctor R D (DGFunctor R PUnit.{1} D) where
  obj := DGQuotient.pointDGFunctor R D
  map := dgPointFamilyHom R D
  map_id x := by
    apply dgFunctorHom_ext
    intro a
    change eId (Complex R) x ≫ dgPointFamilyHom R D x x ≫ dgFunctorHomπ R PUnit.{1} D _ _ a =
      dgFunctorIdentity R PUnit.{1} D _ ≫ dgFunctorHomπ R PUnit.{1} D _ _ a
    rw [dgPointFamilyHom_π, Category.comp_id, dgFunctorIdentity_π]
    rfl
  map_comp x y z := by
    apply dgFunctorHom_ext
    intro a
    change eComp (Complex R) x y z ≫ dgPointFamilyHom R D x z ≫
      dgFunctorHomπ R PUnit.{1} D _ _ a =
      (dgPointFamilyHom R D x y ⊗ₘ dgPointFamilyHom R D y z) ≫
        dgFunctorComposition R PUnit.{1} D _ _ _ ≫ dgFunctorHomπ R PUnit.{1} D _ _ a
    rw [dgPointFamilyHom_π, Category.comp_id, dgFunctorComposition_π,
      tensorHom_comp_tensorHom_assoc, dgPointFamilyHom_π, dgPointFamilyHom_π,
      tensorHom_id, id_whiskerRight, Category.id_comp]
    rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
