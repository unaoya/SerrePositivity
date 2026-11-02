module
public import SerrePositivity.DifferentialGraded.Verdier.Comparison
public import SerrePositivity.Asymptotic.PaperRankQuotient

/-! # 完備化と Verdier 商の順序交換正方形の構造

dg の局所 perfect 比較と論文の列比較を、同じ順序交換正方形の特殊化として公開する。
-/
@[expose] public section
noncomputable section
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Functor Idempotents Limits
section Order
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
  (P : ObjectProperty C) [P.IsTriangulated]

instance firstToLastFactorsCommShift : NatTrans.CommShift (karoubiFirstToLastFactors P).hom ℤ := by
  dsimp [karoubiFirstToLastFactors]
  infer_instance
instance completedFirstToLastFactorsCommShift :
    NatTrans.CommShift (completedKaroubiFirstToLastFactors P).hom ℤ := by
  exact karoubiExtensionOneFactors_commShift (karoubiFirstToLast P)

/-- 既存の順序交換同値と元の商への標準関手が作る正方形。 -/
def orderSquare : karoubiFirstFromOriginal P ⋙ (karoubiVerdierOrderEquivalence P).functor ≅
    P.trW.Q ⋙ toKaroubi _ :=
  Functor.associator (toKaroubi C)
    ((karoubiNullEnvelope P).trW.Q ⋙ toKaroubi _) (completedKaroubiFirstToLast P) ≪≫
  isoWhiskerLeft (toKaroubi C)
    (Functor.associator (karoubiNullEnvelope P).trW.Q (toKaroubi _)
      (completedKaroubiFirstToLast P)) ≪≫
  isoWhiskerLeft (toKaroubi C) (isoWhiskerLeft (karoubiNullEnvelope P).trW.Q
    (completedKaroubiFirstToLastFactors P)) ≪≫
  isoWhiskerLeft (toKaroubi C) (karoubiFirstToLastFactors P) ≪≫
    (functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app P.trW.Q

instance orderSquareCommShift : NatTrans.CommShift (orderSquare P).hom ℤ := by
  let : NatTrans.CommShift (show toKaroubi C ⋙ (functorExtension₂ _ _).obj P.trW.Q ⟶
      P.trW.Q ⋙ toKaroubi _ from
      ((functorExtension₂CompWhiskeringLeftToKaroubiIso _ _).app P.trW.Q).hom) ℤ :=
    karoubiExtensionFactors_commShift P.trW.Q
  dsimp only [orderSquare, Iso.trans_hom, isoWhiskerLeft_hom]
  infer_instance

/-- スカラー倍した射にも、同じ正方形が線形な自然性を与える。 -/
lemma orderSquare_naturality_smul (R : Type*) [CommRing R] [Linear R C]
    {X Y : C} (r : R) (f : X ⟶ Y) :
    (karoubiFirstFromOriginal P ⋙ (karoubiVerdierOrderEquivalence P).functor).map (r • f) ≫
        (orderSquare P).hom.app Y =
      r • ((orderSquare P).hom.app X ≫ (P.trW.Q ⋙ toKaroubi _).map f) := by
  rw [CategoryTheory.Functor.map_smul, Linear.smul_comp]
  exact congrArg (fun t => r • t) ((orderSquare P).hom.naturality f)

/-- 順序交換正方形が与える、実際の三角形関手間の自然同型。 -/
def orderSquareTriangle :
    (karoubiFirstFromOriginal P ⋙ (karoubiVerdierOrderEquivalence P).functor).mapTriangle ≅
      (P.trW.Q ⋙ toKaroubi _).mapTriangle :=
  Functor.mapTriangleIso (orderSquare P)

end Order

namespace DGQuotient
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma triaKaroubiComparison_eq_orderSquare (S : Set D) :
    triaKaroubiComparison A D S = orderSquare (triaImage A D S) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [triaKaroubiComparison, orderSquare, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Functor.associator_hom_app,
    Functor.comp_obj, Category.id_comp]
  exact (Category.id_comp _).symm
instance triaKaroubiComparisonCommShift (S : Set D) :
    NatTrans.CommShift (triaKaroubiComparison A D S).hom ℤ := by
  rw [triaKaroubiComparison_eq_orderSquare]
  infer_instance

instance localPerfectKaroubiFirstEquivalenceFunctorCommShift (S : Set D) (h : localKFlat A D S) :
    (localPerfectKaroubiFirstEquivalence A D S h).functor.CommShift ℤ := by
  dsimp [localPerfectKaroubiFirstEquivalence]
  infer_instance
instance localPerfectKaroubiFirstEquivalenceInverseCommShift (S : Set D) (h : localKFlat A D S) :
    (localPerfectKaroubiFirstEquivalence A D S h).inverse.CommShift ℤ :=
  (localPerfectKaroubiFirstEquivalence A D S h).commShiftInverse ℤ
instance localPerfectKaroubiFirstEquivalenceCommShift (S : Set D) (h : localKFlat A D S) :
    (localPerfectKaroubiFirstEquivalence A D S h).CommShift ℤ :=
  (localPerfectKaroubiFirstEquivalence A D S h).commShift_of_functor ℤ
instance localPerfectKaroubiFirstEquivalenceFunctorIsTriangulated
    (S : Set D) (h : localKFlat A D S) :
    (localPerfectKaroubiFirstEquivalence A D S h).functor.IsTriangulated := by
  change ((localPerfectQuotientEquivalence A D S h).functor ⋙
    (triaKaroubiOrderEquivalence A D S).inverse).IsTriangulated
  infer_instance
instance localPerfectKaroubiFirstEquivalenceIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (localPerfectKaroubiFirstEquivalence A D S h).IsTriangulated :=
  Equivalence.IsTriangulated.mk' (localPerfectKaroubiFirstEquivalence A D S h) inferInstance

/-- 結合比較を明記した、局所 perfect 比較への後置正方形。 -/
def localPerfectOrderSquare (S : Set D) (h : localKFlat A D S) :
    triaKaroubiFirst A D S ⋙ (triaKaroubiOrderEquivalence A D S).functor ⋙
        (localPerfectQuotientEquivalence A D S h).inverse ≅
      triaQuotient A D S ⋙ toKaroubi _ ⋙
        (localPerfectQuotientEquivalence A D S h).inverse :=
  (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (triaKaroubiComparison A D S)
      (localPerfectQuotientEquivalence A D S h).inverse ≪≫ Functor.associator _ _ _

instance localPerfectOrderSquareCommShift (S : Set D) (h : localKFlat A D S) :
    NatTrans.CommShift (localPerfectOrderSquare A D S h).hom ℤ := by
  dsimp only [localPerfectOrderSquare, Iso.trans_hom, isoWhiskerRight_hom, Iso.symm_hom]
  infer_instance

lemma localPerfectPaperSequenceComparison_eq (S : Set D) (h : localKFlat A D S) :
    localPerfectPaperSequenceComparison A D S h = localPerfectOrderSquare A D S h := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [localPerfectPaperSequenceComparison, localPerfectOrderSquare, Iso.trans_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app, Iso.symm_hom,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp, Category.comp_id]

/-- 元の正方形そのものも整数 shift と可換。 -/
instance localPerfectPaperSequenceComparisonCommShift (S : Set D) (h : localKFlat A D S) :
    NatTrans.CommShift (localPerfectPaperSequenceComparison A D S h).hom ℤ := by
  rw [localPerfectPaperSequenceComparison_eq]
  infer_instance

/-- perfect 比較への後置正方形を三角形関手にも公開する。 -/
def localPerfectOrderSquareTriangle (S : Set D) (h : localKFlat A D S) :
    (triaKaroubiFirst A D S ⋙ (triaKaroubiOrderEquivalence A D S).functor ⋙
        (localPerfectQuotientEquivalence A D S h).inverse).mapTriangle ≅
      (triaQuotient A D S ⋙ toKaroubi _ ⋙
        (localPerfectQuotientEquivalence A D S h).inverse).mapTriangle :=
  Functor.mapTriangleIso (localPerfectPaperSequenceComparison A D S h)

end DGQuotient

section Paper
open SerrePositivity.Asymptotic
variable (R : Type u) [CommRing R] [Nontrivial R] (s : ℕ → ℕ)

lemma paperSequenceComparison_eq_orderSquare :
    paperSequenceComparison R s = orderSquare (rankSmallBounded (R := R) (s := s)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  simp only [paperSequenceComparison, orderSquare, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, Functor.associator_hom_app,
    Functor.comp_obj, Category.id_comp]
  exact (Category.id_comp _).symm

instance paperSequenceComparisonCommShift :
    NatTrans.CommShift (paperSequenceComparison R s).hom ℤ := by
  rw [paperSequenceComparison_eq_orderSquare]
  infer_instance
/-- 論文の列比較そのものの三角形関手に対する正方形。 -/
def paperSequenceComparisonTriangle :
    (paperSequenceFunctor R s ⋙ (paperRankEquivalence R s).functor).mapTriangle ≅
      (completedSequenceFunctor (R := R) (s := s)).mapTriangle :=
  Functor.mapTriangleIso (paperSequenceComparison R s)

end Paper
end SerrePositivity.DifferentialGraded
