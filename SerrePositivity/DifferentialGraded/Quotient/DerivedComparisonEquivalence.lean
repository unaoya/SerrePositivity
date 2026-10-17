module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonFullFaithful

/-! # 局所 K-flat 版の tria(D)/tria(S) と tria(D/S) の同値 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma derivedQuotientLift_finiteCell (S : Set D) (X : TriaQuotient A D S) :
    derivedFiniteCellOver A (QuotientObject D S) Set.univ
      ((derivedQuotientLift A D S).obj X) := by
  let Q := triaQuotient A D S
  let P := derivedFiniteCellOver A (QuotientObject D S) Set.univ
  exact P.prop_of_iso ((derivedQuotientLift A D S).mapIso (Q.objObjPreimageIso X))
    (P.prop_of_iso ((derivedQuotientLiftFactors A D S).app (Q.objPreimage X)).symm
      (derivedComparisonFromTria_finiteCell A D S (Q.objPreimage X)))

/-- 指定 Verdier 商から明示的 dg 商の tria への実際の導来延長。 -/
def localQuotientTriaFunctor (S : Set D) :
    TriaQuotient A D S ⥤ TriaCategory A (QuotientObject D S) :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).lift
    (derivedQuotientLift A D S) (derivedQuotientLift_finiteCell A D S)

instance localQuotientTriaFunctorCommShift (S : Set D) :
    (localQuotientTriaFunctor A D S).CommShift ℤ := by
  dsimp [localQuotientTriaFunctor]
  infer_instance
instance localQuotientTriaFunctorIsTriangulated (S : Set D) :
    (localQuotientTriaFunctor A D S).IsTriangulated := by
  dsimp [localQuotientTriaFunctor]
  infer_instance

/-- 値域を充満部分圏に制限しても、同じ射写像の充満忠実性を保つ。 -/
def localQuotientTriaFullyFaithful (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaFunctor A D S).FullyFaithful where
  preimage f := (derivedQuotientLiftFullyFaithful A D S h).preimage
    ((triaInclusion A (QuotientObject D S)).map f)
  map_preimage f := by
    apply (triaInclusion A (QuotientObject D S)).map_injective
    exact (derivedQuotientLiftFullyFaithful A D S h).map_preimage _
  preimage_map f := (derivedQuotientLiftFullyFaithful A D S h).preimage_map f

/-- 商内の代表対象の像の具体的な計算。 -/
def localQuotientTriaRepresentableIso (S : Set D) (z : D) :
    (localQuotientTriaFunctor A D S).obj
        ((triaQuotient A D S).obj (triaRepresentable A D z)) ≅
      triaRepresentable A (QuotientObject D S) ⟨z⟩ :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).isoMk
    ((derivedQuotientLiftFactors A D S).app (triaRepresentable A D z) ≪≫
      derivedExtensionRepresentableUnitIso A D (QuotientObject D S) (inclusion A D S) z)

lemma localQuotientTriaFunctor_essSurj (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaFunctor A D S).EssSurj := by
  let : (localQuotientTriaFunctor A D S).Full := (localQuotientTriaFullyFaithful A D S h).full
  refine ⟨fun X => ?_⟩
  have hle := (triaImage_le_iff_generators A (QuotientObject D S) Set.univ
    (localQuotientTriaFunctor A D S).essImage).2 (fun z _ =>
      ⟨(triaQuotient A D S).obj (triaRepresentable A D z.val),
        ⟨localQuotientTriaRepresentableIso A D S z.val⟩⟩)
  exact hle X X.property

/-- 局所 K-flat 仮定から得る、指定 Verdier 商と明示的 dg 商の tria の同値。 -/
def localQuotientTriaEquivalence (S : Set D) (h : localKFlat A D S) :
    TriaQuotient A D S ≌ TriaCategory A (QuotientObject D S) := by
  let : (localQuotientTriaFunctor A D S).Full := (localQuotientTriaFullyFaithful A D S h).full
  let : (localQuotientTriaFunctor A D S).Faithful :=
    (localQuotientTriaFullyFaithful A D S h).faithful
  let : (localQuotientTriaFunctor A D S).EssSurj := localQuotientTriaFunctor_essSurj A D S h
  let : (localQuotientTriaFunctor A D S).IsEquivalence := {}
  exact (localQuotientTriaFunctor A D S).asEquivalence

/-- M9 の商を取る前の Hom が次数零に集中して平坦である場合の入口。 -/
def localQuotientTriaEquivalence_of_flat_zero (S : Set D)
    (hz : ∀ (x y : D) (i : ℤ), i ≠ 0 → IsZero ((x ⟶[Complex A] y).X i))
    (hf : ∀ x y : D, Module.Flat A ((x ⟶[Complex A] y).X 0)) :
    TriaQuotient A D S ≌ TriaCategory A (QuotientObject D S) :=
  localQuotientTriaEquivalence A D S
    (allHomKFlat_local A D (allHomKFlat_of_flat_zero A D hz hf) S)

end SerrePositivity.DifferentialGraded.DGQuotient
