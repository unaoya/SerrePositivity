module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryCochain

/-! # cell付加の関手延長に指定する原始元とその評価cochain -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I) (E : Type z) [DGCategory A E] (F : DGFunctor A D E)

/-- 各cellの像を指定し、微分が元の境界の像になることを要求する。 -/
structure PrimitiveData where
  primitive : ∀ i, (homObject A E (F.obj (C.source i)) (F.obj (C.target i))).X (C.degree i)
  boundary : ∀ i, (homObject A E (F.obj (C.source i)) (F.obj (C.target i))).d
    (C.degree i) (C.degree i + 1) (primitive i) =
      (F.map (C.source i) (C.target i)).f (C.degree i + 1) (C.boundary i).val

namespace PrimitiveData
variable {A D I C E F} (P : PrimitiveData A D I C E F)

/-- 原始元は一般に閉じていないため、まず次数0 cochainとして評価する。 -/
def cochain (i : I) : Cochain (C.generator A D I i)
    (homObject A E (F.obj (C.source i)) (F.obj (C.target i))) 0 :=
  Cochain.fromSingleMk (p := C.degree i) (q := C.degree i)
    (moduleElementMap A _ (P.primitive i)) (add_zero _)

lemma cochain_generator (i : I) :
    (P.cochain i).v (C.degree i) (C.degree i) (add_zero _)
      ((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv (1 : A)) =
    P.primitive i := by
  rw [cochain, Cochain.fromSingleMk_v]
  change (moduleElementMap A _ (P.primitive i))
    (((singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).inv ≫
      (singleObjXSelf (.up ℤ) (C.degree i) (𝟙_ (ModuleCat.{u} A))).hom) (1 : A)) = _
  rw [Iso.inv_hom_id]
  exact one_smul A (P.primitive i)

/-- 原始元評価の微分は指定境界の関手像。 -/
lemma cochain_differential (i : I) :
    δ 0 1 (P.cochain i) = (C.boundaryCochain A D I i).comp
      (Cochain.ofHom (F.map (C.source i) (C.target i))) (add_zero 1) := by
  rw [cochain, Cochain.δ_fromSingleMk _ _ 1 (C.degree i + 1) (by omega),
    boundaryCochain, ← Cochain.fromSingleMk_postcomp]
  congr 1
  apply (moduleElementEquiv A _).injective
  change (homObject A E (F.obj (C.source i)) (F.obj (C.target i))).d
    (C.degree i) (C.degree i + 1) ((1 : A) • P.primitive i) =
    (F.map (C.source i) (C.target i)).f (C.degree i + 1) ((1 : A) • (C.boundary i).val)
  rw [one_smul, one_smul]
  exact P.boundary i

end PrimitiveData
end SerrePositivity.DifferentialGraded.DGCellAttachment.Family

namespace SerrePositivity.DifferentialGraded

namespace DGCategoryBoundaryCells
open SerrePositivity.DifferentialGraded.DGCellAttachment
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type z) [DGCategory A E] (F : DGFunctor A D E)

/-- 全境界cellの族には、添字自身が持つ指定原始元がある。 -/
def primitiveData : Family.PrimitiveData A D (Index A D E F) (boundaryFamily A D E F) E F where
  primitive i := i.2.2.primitive
  boundary i := i.2.2.boundary

end DGCategoryBoundaryCells
end SerrePositivity.DifferentialGraded
