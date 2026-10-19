module

public import SerrePositivity.InfinityCategories.F1.LeftStraighteningInfinityReconstruction
public import SerrePositivity.InfinityCategories.F1.RelativeFunctorComparisonEquivalence
public import SerrePositivity.InfinityCategories.F1.SmallLeftUnstraighteningMappingSpace
public import SerrePositivity.InfinityCategories.F1.CoherentUnstraighteningMappingEquivalence

/-!
概要：実際の対象図式の変換空間と元の left fibrations の写像空間の比較同値。
方針：実際の復元射で相対 Hom を置き換え、縮小同型と unstraightening の比較同値を合成する。
規約：比較の順方向を分類写像の pinchedHomMap と同一視する証明は別途必要。
使われ方：実際の分類写像の全高次の作用と照合する比較射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 実際の復元射による二つの相対写像空間の比較同値。 -/
def leftStraighteningInfinityRelativeReconstructionEquivalence {E F B : SSet.{u}}
    [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q] :
    QCatEquivalence (relativeFunctorSpace q p)
      (relativeFunctorSpace
        (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q))
        (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p))) := by
  have : LeftFibration (Over.mk q).hom := inferInstanceAs (LeftFibration q)
  have : LeftFibration (Over.mk
      (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q))).hom :=
    inferInstanceAs (LeftFibration
      (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)))
  exact relativeFunctorEquivalenceOfComparisons
    (Over.mk p)
    (Over.mk (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram p)))
    (Over.mk q)
    (Over.mk (smallLeftUnstraighteningProjection (leftStraighteningInfinityDiagram q)))
    (Over.homMk (leftStraighteningInfinityReconstruction p)
      (leftStraighteningInfinityReconstruction_projection p))
    (Over.homMk (leftStraighteningInfinityReconstruction q)
      (leftStraighteningInfinityReconstruction_projection q))
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence p)
    (leftStraighteningInfinityReconstruction_isPrecompositionEquivalence q)

/-- 相対 Hom の持ち上げと、実際の対象図式の変換空間を比較する同値。 -/
def leftStraighteningInfinityRelativeMappingEquivalence {E F B : SSet.{u}}
    [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q] :
    QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj (relativeFunctorSpace q p))
      (pinchedHom (functorVertex (leftStraighteningInfinityDiagram p))
        (functorVertex (leftStraighteningInfinityDiagram q))) := by
  have e := (leftStraighteningInfinityRelativeReconstructionEquivalence p q).isQCatEquivalence.ulift
  exact (e.choose.trans (qCatEquivalenceOfIso (smallLeftUnstraighteningRelativeFunctorIso
    (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q)))).trans
      (leftUnstraighteningPinchedMappingSpaceMap_isQCatEquivalence
        (leftStraighteningInfinityDiagram p) (leftStraighteningInfinityDiagram q)).choose.symm

/-- coherent nerve の実際の写像空間と、実際の対象図式の変換空間の比較同値。 -/
def leftStraighteningInfinityMappingComparisonEquivalence {E F B : SSet.{u}}
    [Quasicategory B] (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q] :
    QCatEquivalence (pinchedHom (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q))
      (pinchedHom (functorVertex (leftStraighteningInfinityDiagram p))
        (functorVertex (leftStraighteningInfinityDiagram q))) :=
  (leftFibrationInfinityMappingEquivalence p q).symm.trans
    (leftStraighteningInfinityRelativeMappingEquivalence p q)

/-- 実際の分類写像の写像空間への作用を、実際の対象図式の端点表示に揃える同型。 -/
def leftStraighteningInfinityMappingEndpointIso {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q] :
    pinchedHom
      ((leftStraighteningInfinityMap B).app (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p))
      ((leftStraighteningInfinityMap B).app (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex q)) ≅
    pinchedHom (functorVertex (leftStraighteningInfinityDiagram p))
      (functorVertex (leftStraighteningInfinityDiagram q)) :=
  eqToIso (congrArg₂ (fun a b ↦ pinchedHom a b)
    (leftStraighteningInfinityDiagram_vertex p).symm
    (leftStraighteningInfinityDiagram_vertex q).symm)

/-- 分類写像自体の全写像空間への作用。比較同値との照合で使う実際の射。 -/
def leftStraighteningInfinityPinchedHomMap {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q] :
    pinchedHom (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q) ⟶
      pinchedHom (functorVertex (leftStraighteningInfinityDiagram p))
        (functorVertex (leftStraighteningInfinityDiagram q)) :=
  pinchedHomMap (leftStraighteningInfinityMap B)
    (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q) ≫
      (leftStraighteningInfinityMappingEndpointIso p q).hom

/-- 端点表示の変更は、実際の分類写像の写像空間での同値性を変えない。 -/
lemma leftStraighteningInfinityPinchedHomMap_isQCatEquivalence_iff {E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q] :
    IsQCatEquivalence (leftStraighteningInfinityPinchedHomMap p q) ↔
      IsQCatEquivalence (pinchedHomMap (leftStraighteningInfinityMap B)
        (leftFibrationInfinityVertex p) (leftFibrationInfinityVertex q)) := by
  have he := (qCatEquivalenceOfIso
    (leftStraighteningInfinityMappingEndpointIso p q)).isQCatEquivalence
  exact ⟨fun h ↦ he.cancel_right h, fun h ↦ h.comp he⟩

end SerrePositivity.InfinityCategories
