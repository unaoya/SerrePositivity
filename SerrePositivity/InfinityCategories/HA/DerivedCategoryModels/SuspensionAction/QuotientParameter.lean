module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction.ConeData
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparison.Filtration

/-!
概要：正本 strict data の指定収縮を保持した、同じ実懸垂間の全次数変換の延長入口。
方針：実商の parameterExtension を、既存 data の同じ resolved・perfect 集合に適用する。
規約：ε との整合を明示し、未構成の resolved パラメータ作用から存在を推論しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
open CategoryTheory DifferentialGraded KST.NonConnective KST.SConstruction
variable (R : Type u) [CommRing R] (C D : Type v)
  [DGCategory R C] [Small.{u} C] [DGCategory R D] [Small.{u} D]
  {κ : Cardinal.{u}} (I : DGKappaConeInput R C κ) (J : DGKappaConeInput R D κ)
local notation "PC" => DGCategoryCellResolution.Source R (DGKappaCone R C I)
local notation "PD" => DGCategoryCellResolution.Source R (DGKappaCone R D J)
local notation "SC" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R C I)
  (dgKappaConePerfectObjects R C I)
local notation "SD" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGNullObjects R (DGKappaCone R D J)
  (dgKappaConePerfectObjects R D J)

/-- 正本 data が指定する同じ ε を持つ contracted functor。 -/
def dgSuspensionMapContractedFunctor (M : DGKappaSuspensionMapData R C D I J) :
    DGQuotient.ContractedFunctor R PC SC (DGKappaSuspension R D J) :=
  DGQuotient.functorContracted R PC PD M.resolved SC SD
    (dgKappaSuspensionMap_preservesNullObjects R C D I J M)

variable (F G : DGKappaSuspensionMapData R C D I J) {K : Complex R}
  (τ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K)
    (dgSuspensionMapContractedFunctor R C D I J F).toDGFunctor
    (dgSuspensionMapContractedFunctor R C D I J G).toDGFunctor)

/-- resolved パラメータが指定 ε と整合すれば、同じ実商関手間へ厳密延長する。 -/
def dgSuspensionQuotientParameter
    (hε : ∀ (b : SC) (k : ℤ) (t : K.X k),
      forward R (p := -1) (q := k) (n := -1 + k)
        ((dgSuspensionMapContractedFunctor R C D I J F).homotopy b)
        ((τ.app b.val).f k t) rfl =
      (k * (-1)).negOnePow • forward R (p := k) (q := -1) (n := -1 + k) ((τ.app b.val).f k t)
        ((dgSuspensionMapContractedFunctor R C D I J G).homotopy b) (by omega)) :
    GradedNatTrans ((Center.ofBraided (Complex R)).obj K)
      (dgKappaSuspensionInputMap R C D I J F).down
      (dgKappaSuspensionInputMap R C D I J G).down :=
  DGQuotient.parameterExtension R
    (dgSuspensionMapContractedFunctor R C D I J F)
    (dgSuspensionMapContractedFunctor R C D I J G) τ hε

include τ in
/-- 同じ成分を保つ厳密延長に必要な、固定 ε との整合条件。 -/
lemma dgSuspensionQuotientParameter_epsilon_necessary
    (σ : GradedNatTrans ((Center.ofBraided (Complex R)).obj K)
      (dgKappaSuspensionInputMap R C D I J F).down
      (dgKappaSuspensionInputMap R C D I J G).down)
    (hσ : ∀ x : PC, σ.app ⟨x⟩ = τ.app x)
    (b : SC) (k : ℤ) (t : K.X k) :
    forward R (p := -1) (q := k) (n := -1 + k)
        ((dgSuspensionMapContractedFunctor R C D I J F).homotopy b)
      ((τ.app b.val).f k t) rfl =
    (k * (-1)).negOnePow • forward R (p := k) (q := -1) (n := -1 + k) ((τ.app b.val).f k t)
      ((dgSuspensionMapContractedFunctor R C D I J G).homotopy b) (by omega) :=
  DGQuotient.parameterExtension_epsilon_necessary R
    (dgSuspensionMapContractedFunctor R C D I J F)
    (dgSuspensionMapContractedFunctor R C D I J G) τ σ hσ b k t

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SuspensionAction
