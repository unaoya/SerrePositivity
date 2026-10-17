module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonExtension
public import SerrePositivity.DifferentialGraded.Verdier.FiniteCellHomotopy

/-! # 有限 cell の三角モデルによる dg 商比較と Verdier 因子化

局所 K-flat 性を要する完全忠実性に先立ち、実際の三角関手とその因子化を構成する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

local instance (S : Set D) : (dgModuleExtension A D (QuotientObject D S)
    (inclusion A D S)).onClosed.CommShift ℤ :=
  dgModuleFunctorCommShift A D _ _
local instance (S : Set D) : (dgModuleExtension A D (QuotientObject D S)
    (inclusion A D S)).onHomotopy.CommShift ℤ :=
  dgModuleFunctorHomotopyCommShift A D _ _
local instance (S : Set D) : (dgModuleExtension A D (QuotientObject D S)
    (inclusion A D S)).onHomotopy.IsTriangulated :=
  dgModuleFunctorHomotopyIsTriangulated A D _ _

/-- 有限 cell の K(D) モデル上で graph tensor を使う比較。 -/
def quotientCellToDerived (S : Set D) :
    HomotopyFiniteCellCategoryOver A D Set.univ ⥤ DerivedModuleCategory A (QuotientObject D S) :=
  (homotopyFiniteCellOver A D Set.univ).ι ⋙
    (dgModuleExtension A D (QuotientObject D S) (inclusion A D S)).onHomotopy ⋙
      moduleHomotopyToDerivedClosed A (QuotientObject D S)

instance quotientCellToDerivedCommShift (S : Set D) :
    (quotientCellToDerived A D S).CommShift ℤ := by
  dsimp [quotientCellToDerived]
  infer_instance
instance quotientCellToDerivedIsTriangulated (S : Set D) :
    (quotientCellToDerived A D S).IsTriangulated := by
  dsimp [quotientCellToDerived]
  infer_instance

/-- 三角同値の逆関手を使うことで、tria 上に整合的な整数 shift と三角性を保つ。 -/
def quotientTriaToDerived (S : Set D) :
    TriaCategory A D ⥤ DerivedModuleCategory A (QuotientObject D S) :=
  (homotopyFiniteCellTriaEquivalence A D Set.univ).inverse ⋙ quotientCellToDerived A D S

instance quotientTriaToDerivedCommShift (S : Set D) :
    (quotientTriaToDerived A D S).CommShift ℤ := by
  dsimp [quotientTriaToDerived]
  infer_instance
instance quotientTriaToDerivedIsTriangulated (S : Set D) :
    (quotientTriaToDerived A D S).IsTriangulated := by
  dsimp [quotientTriaToDerived]
  infer_instance

lemma quotientCellToDerived_finiteCell (S : Set D)
    (X : HomotopyFiniteCellCategoryOver A D Set.univ) :
    derivedFiniteCellOver A (QuotientObject D S) Set.univ
      ((quotientCellToDerived A D S).obj X) := by
  obtain ⟨M, ⟨c⟩, ⟨e⟩⟩ := X.property
  let P := derivedFiniteCellOver A (QuotientObject D S) Set.univ
  have h := finiteCellCode_image_mem A D (QuotientObject D S)
    ((dgModuleExtension A D (QuotientObject D S) (inclusion A D S)).onClosed ⋙
      moduleToDerived A (QuotientObject D S))
    (graphExtension_cone_distinguished A D (QuotientObject D S) (inclusion A D S)) P
    (fun x _ => P.prop_of_iso ((moduleToDerived A (QuotientObject D S)).mapIso
      (dgModuleExtensionRepresentableIso A D (QuotientObject D S) (inclusion A D S) x)).symm
      ((moduleFiniteCellOver A (QuotientObject D S) Set.univ).prop_map_obj
        (moduleToDerived A (QuotientObject D S))
        (moduleFiniteCell_representable A (QuotientObject D S) ⟨x⟩))) c
  exact P.prop_of_iso
    ((dgExtensionHomotopyToDerived A D (QuotientObject D S) (inclusion A D S)).mapIso e)
    (P.prop_of_iso (dgExtensionHomotopyComputation A D (QuotientObject D S)
      (inclusion A D S) M).symm h)

/-- 明示的商への比較を、商側 tria に値を持つ三角関手として構成。 -/
def quotientTriaFunctor (S : Set D) : TriaCategory A D ⥤ TriaCategory A (QuotientObject D S) :=
  (derivedFiniteCellOver A (QuotientObject D S) Set.univ).lift (quotientTriaToDerived A D S)
    (fun _ => quotientCellToDerived_finiteCell A D S _)

instance quotientTriaFunctorCommShift (S : Set D) :
    (quotientTriaFunctor A D S).CommShift ℤ := by
  dsimp [quotientTriaFunctor]
  infer_instance
instance quotientTriaFunctorIsTriangulated (S : Set D) :
    (quotientTriaFunctor A D S).IsTriangulated := by
  dsimp [quotientTriaFunctor]
  infer_instance

/-- 三角モデルにおける代表対象。 -/
def homotopyCellRepresentable (x : D) : HomotopyFiniteCellCategoryOver A D Set.univ :=
  ⟨(moduleToHomotopy A D).obj (ForgetEnrichment.of (Complex A) (representable A x)),
    (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToHomotopy A D)
      (moduleFiniteCell_representable A D x)⟩

def homotopyCellRepresentableIso (x : D) :
    (homotopyFiniteCellTriaEquivalence A D Set.univ).functor.obj (homotopyCellRepresentable A D x) ≅
      triaRepresentable A D x :=
  (derivedFiniteCellOver A D Set.univ).isoMk ((moduleToHomotopyDerivedIso A D).app _)

/-- 実際の三角比較も、空 path の像の代表加群として計算できる。 -/
def quotientTriaFunctor_representableIso (S : Set D) (x : D) :
    (quotientTriaFunctor A D S).obj (triaRepresentable A D x) ≅
      triaRepresentable A (QuotientObject D S) ⟨x⟩ := by
  let e := homotopyFiniteCellTriaEquivalence A D Set.univ
  let t := e.inverse.mapIso (homotopyCellRepresentableIso A D x).symm ≪≫
    (e.unitIso.app (homotopyCellRepresentable A D x)).symm
  exact (derivedFiniteCellOver A (QuotientObject D S) Set.univ).isoMk
    ((quotientCellToDerived A D S).mapIso t ≪≫
      dgExtensionHomotopyComputation A D (QuotientObject D S) (inclusion A D S) _ ≪≫
      (moduleToDerived A (QuotientObject D S)).mapIso
        (dgModuleExtensionRepresentableIso A D (QuotientObject D S) (inclusion A D S) x))

lemma quotientTriaFunctor_kills (S : Set D) :
    triaImage A D S ≤ triangulatedKernel (quotientTriaFunctor A D S) := by
  refine (triaImage_le_iff_generators A D S
    (triangulatedKernel (quotientTriaFunctor A D S))).2 ?_
  intro x hx
  rw [triangulatedKernel, IsZero.iff_id_eq_zero]
  apply (triaInclusion A (QuotientObject D S)).map_injective
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  have h := (quotientRepresentable_derived_isZero A D S ⟨x, hx⟩).of_iso
    ((triaInclusion A (QuotientObject D S)).mapIso (quotientTriaFunctor_representableIso A D S x))
  exact h.eq_of_src _ _

/-- tria(S) の cone を持つ Verdier 分母は、実際の比較で可逆になる。 -/
lemma quotientTriaFunctor_inverts (S : Set D) :
    (triaImage A D S).trW.IsInvertedBy (quotientTriaFunctor A D S) := by
  intro X Y f hf
  exact (triangulatedKernel_trW_iff (quotientTriaFunctor A D S) f).1
    ((triaImage A D S).trW_monotone (quotientTriaFunctor_kills A D S) _ hf)

/-- 局所 K-flat 比較で完全忠実性を証明すべき、指定された実際の関手。 -/
def quotientVerdierComparison (S : Set D) :
    TriaQuotient A D S ⥤ TriaCategory A (QuotientObject D S) :=
  Localization.lift (quotientTriaFunctor A D S) (quotientTriaFunctor_inverts A D S)
    (triaQuotient A D S)

/-- U17a の指定局所化と実際の三角比較との因子化同型。 -/
def quotientVerdierComparisonFactors (S : Set D) :
    triaQuotient A D S ⋙ quotientVerdierComparison A D S ≅ quotientTriaFunctor A D S :=
  Localization.fac (quotientTriaFunctor A D S) (quotientTriaFunctor_inverts A D S)
    (triaQuotient A D S)

instance quotientVerdierComparisonLifting (S : Set D) :
    Localization.Lifting (triaQuotient A D S) (triaImage A D S).trW
      (quotientTriaFunctor A D S) (quotientVerdierComparison A D S) :=
  Localization.liftingLift (quotientTriaFunctor A D S) (quotientTriaFunctor_inverts A D S)
    (triaQuotient A D S)

instance quotientVerdierComparisonCommShift (S : Set D) :
    (quotientVerdierComparison A D S).CommShift ℤ :=
  Functor.commShiftOfLocalization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (quotientTriaFunctor A D S) (quotientVerdierComparison A D S)

instance quotientVerdierComparisonFactorsCommShift (S : Set D) :
    NatTrans.CommShift (quotientVerdierComparisonFactors A D S).hom ℤ :=
  NatTrans.commShift_iso_hom_of_localization (triaQuotient A D S) (triaImage A D S).trW ℤ
    (quotientTriaFunctor A D S) (quotientVerdierComparison A D S)

instance quotientVerdierComparisonIsTriangulated (S : Set D) :
    (quotientVerdierComparison A D S).IsTriangulated := by
  have : (triaQuotient A D S).mapArrow.EssSurj :=
    Localization.essSurj_mapArrow (triaQuotient A D S) (triaImage A D S).trW
  exact Functor.isTriangulated_of_precomp_iso (quotientVerdierComparisonFactors A D S)

/-- 指定した局所化の代表対象について、比較後の代表加群を計算する。 -/
def quotientVerdierComparison_representableIso (S : Set D) (x : D) :
    (quotientVerdierComparison A D S).obj ((triaQuotient A D S).obj (triaRepresentable A D x)) ≅
      triaRepresentable A (QuotientObject D S) ⟨x⟩ :=
  (quotientVerdierComparisonFactors A D S).app (triaRepresentable A D x) ≪≫
    quotientTriaFunctor_representableIso A D S x

/-- 完全性が得られれば、本質像の三角閉性と代表生成性から本質的全射性が従う。 -/
instance quotientVerdierComparisonEssSurj (S : Set D) [(quotientVerdierComparison A D S).Full] :
    (quotientVerdierComparison A D S).EssSurj where
  mem_essImage X := by
    have hle := (triaImage_le_iff_generators A (QuotientObject D S) Set.univ
      (quotientVerdierComparison A D S).essImage).2
      (fun x _ => ⟨(triaQuotient A D S).obj (triaRepresentable A D x.val),
        ⟨quotientVerdierComparison_representableIso A D S x.val⟩⟩)
    exact hle X X.property

end SerrePositivity.DifferentialGraded.DGQuotient
