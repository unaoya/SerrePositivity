module
public import SerrePositivity.DifferentialGraded.Quotient.DerivedComparisonEquivalence
public import SerrePositivity.DifferentialGraded.Verdier.KaroubiTransport
public import SerrePositivity.DifferentialGraded.Perfect.KaroubiEquivalence
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementTriangulated
public import SerrePositivity.DifferentialGraded.Perfect.SmallEnhancementTriangulated

/-! # 局所 K-flat 版の dg 商の perfect enhancement と完備 Verdier 商

U17a の指定 Karoubi 完備化に値を持ち、既存の順序交換比較に接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory Idempotents Functor
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

instance localQuotientTriaEquivalenceFunctorCommShift (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaEquivalence A D S h).functor.CommShift ℤ := by
  change (localQuotientTriaFunctor A D S).CommShift ℤ
  infer_instance

instance localQuotientTriaEquivalenceInverseCommShift (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaEquivalence A D S h).inverse.CommShift ℤ :=
  (localQuotientTriaEquivalence A D S h).commShiftInverse ℤ

instance localQuotientTriaEquivalenceCommShift (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaEquivalence A D S h).CommShift ℤ :=
  (localQuotientTriaEquivalence A D S h).commShift_of_functor ℤ

instance localQuotientTriaEquivalenceFunctorIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaEquivalence A D S h).functor.IsTriangulated := by
  change (localQuotientTriaFunctor A D S).IsTriangulated
  infer_instance

instance localQuotientTriaEquivalenceIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (localQuotientTriaEquivalence A D S h).IsTriangulated :=
  Equivalence.IsTriangulated.mk' (localQuotientTriaEquivalence A D S h) inferInstance

/-- U15e の実際の同値を Karoubi 完備化した同値。 -/
def localCompletedQuotientEquivalence (S : Set D) (h : localKFlat A D S) :
    CompletedTriaQuotient A D S ≌ Karoubi (TriaCategory A (QuotientObject D S)) :=
  karoubiEquivalenceTransport (localQuotientTriaEquivalence A D S h)

instance localCompletedQuotientEquivalenceFunctorCommShift (S : Set D) (h : localKFlat A D S) :
    (localCompletedQuotientEquivalence A D S h).functor.CommShift ℤ := by
  change ((functorExtension₂ _ _).obj (localQuotientTriaEquivalence A D S h).functor).CommShift ℤ
  infer_instance

instance localCompletedQuotientEquivalenceInverseCommShift (S : Set D) (h : localKFlat A D S) :
    (localCompletedQuotientEquivalence A D S h).inverse.CommShift ℤ :=
  (localCompletedQuotientEquivalence A D S h).commShiftInverse ℤ

instance localCompletedQuotientEquivalenceCommShift (S : Set D) (h : localKFlat A D S) :
    (localCompletedQuotientEquivalence A D S h).CommShift ℤ :=
  (localCompletedQuotientEquivalence A D S h).commShift_of_functor ℤ

instance localCompletedQuotientEquivalenceIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (localCompletedQuotientEquivalence A D S h).IsTriangulated :=
  Equivalence.IsTriangulated.mk' (localCompletedQuotientEquivalence A D S h) (by
    change ((functorExtension₂ _ _).obj
      (localQuotientTriaEquivalence A D S h).functor).IsTriangulated
    infer_instance)

/-- U17b：明示的 dg 商の perfect enhancement の H⁰ と指定完備 Verdier 商の同値。 -/
def localPerfectQuotientEquivalence (S : Set D) (h : localKFlat A D S) :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      CompletedTriaQuotient A D S :=
  ((perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).trans
    (finiteCellKaroubiPerfectEquivalence A (QuotientObject D S) Set.univ).symm).trans
      (localCompletedQuotientEquivalence A D S h).symm

instance localPerfectQuotientEquivalenceFunctorCommShift (S : Set D) (h : localKFlat A D S) :
    (localPerfectQuotientEquivalence A D S h).functor.CommShift ℤ := by
  dsimp [localPerfectQuotientEquivalence]
  infer_instance

instance localPerfectQuotientEquivalenceInverseCommShift (S : Set D) (h : localKFlat A D S) :
    (localPerfectQuotientEquivalence A D S h).inverse.CommShift ℤ :=
  (localPerfectQuotientEquivalence A D S h).commShiftInverse ℤ

instance localPerfectQuotientEquivalenceCommShift (S : Set D) (h : localKFlat A D S) :
    (localPerfectQuotientEquivalence A D S h).CommShift ℤ :=
  (localPerfectQuotientEquivalence A D S h).commShift_of_functor ℤ

instance localPerfectQuotientEquivalenceFunctorIsTriangulated
    (S : Set D) (h : localKFlat A D S) :
    (localPerfectQuotientEquivalence A D S h).functor.IsTriangulated := by
  change (((perfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
    (finiteCellKaroubiPerfectEquivalence A (QuotientObject D S) Set.univ).inverse) ⋙
      (localCompletedQuotientEquivalence A D S h).inverse).IsTriangulated
  infer_instance

instance localPerfectQuotientEquivalenceIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (localPerfectQuotientEquivalence A D S h).IsTriangulated :=
  Equivalence.IsTriangulated.mk' (localPerfectQuotientEquivalence A D S h) inferInstance

/-- 小さい dg 代表系の H⁰ を用いた、同じ指定完備 Verdier 商との比較。 -/
def localSmallPerfectQuotientEquivalence (S : Set D) (h : localKFlat A D S) :
    SmallPerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      CompletedTriaQuotient A D S :=
  ((smallPerfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).trans
    (finiteCellKaroubiPerfectEquivalence A (QuotientObject D S) Set.univ).symm).trans
      (localCompletedQuotientEquivalence A D S h).symm

instance localSmallPerfectQuotientEquivalenceFunctorCommShift (S : Set D) (h : localKFlat A D S) :
    (localSmallPerfectQuotientEquivalence A D S h).functor.CommShift ℤ := by
  dsimp [localSmallPerfectQuotientEquivalence]
  infer_instance

instance localSmallPerfectQuotientEquivalenceInverseCommShift (S : Set D) (h : localKFlat A D S) :
    (localSmallPerfectQuotientEquivalence A D S h).inverse.CommShift ℤ :=
  (localSmallPerfectQuotientEquivalence A D S h).commShiftInverse ℤ

instance localSmallPerfectQuotientEquivalenceCommShift (S : Set D) (h : localKFlat A D S) :
    (localSmallPerfectQuotientEquivalence A D S h).CommShift ℤ :=
  (localSmallPerfectQuotientEquivalence A D S h).commShift_of_functor ℤ

instance localSmallPerfectQuotientEquivalenceFunctorIsTriangulated
    (S : Set D) (h : localKFlat A D S) :
    (localSmallPerfectQuotientEquivalence A D S h).functor.IsTriangulated := by
  change (((smallPerfectDGModuleHomotopyEquivalence A (QuotientObject D S) Set.univ).functor ⋙
    (finiteCellKaroubiPerfectEquivalence A (QuotientObject D S) Set.univ).inverse) ⋙
      (localCompletedQuotientEquivalence A D S h).inverse).IsTriangulated
  infer_instance

instance localSmallPerfectQuotientEquivalenceIsTriangulated (S : Set D) (h : localKFlat A D S) :
    (localSmallPerfectQuotientEquivalence A D S h).IsTriangulated :=
  Equivalence.IsTriangulated.mk' (localSmallPerfectQuotientEquivalence A D S h) inferInstance

/-- 同じ比較の、完備化を先に行う側への表示。 -/
def localPerfectKaroubiFirstEquivalence (S : Set D) (h : localKFlat A D S) :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      Karoubi (KaroubiFirstQuotient (triaImage A D S)) :=
  (localPerfectQuotientEquivalence A D S h).trans (triaKaroubiOrderEquivalence A D S).symm

/-- U17c の既存の順序交換比較を、局所 K-flat perfect enhancement の比較へ後置する。 -/
def localPerfectPaperSequenceComparison (S : Set D) (h : localKFlat A D S) :
    triaKaroubiFirst A D S ⋙ (triaKaroubiOrderEquivalence A D S).functor ⋙
        (localPerfectQuotientEquivalence A D S h).inverse ≅
      triaQuotient A D S ⋙ toKaroubi _ ⋙
        (localPerfectQuotientEquivalence A D S h).inverse :=
  isoWhiskerRight (triaKaroubiComparison A D S)
    (localPerfectQuotientEquivalence A D S h).inverse

/-- M9 の次数零の平坦 Hom を入力とする U17b の同値。 -/
def localPerfectQuotientEquivalence_of_flat_zero (S : Set D)
    (hz : ∀ (x y : D) (i : ℤ), i ≠ 0 → Limits.IsZero ((x ⟶[Complex A] y).X i))
    (hf : ∀ x y : D, Module.Flat A ((x ⟶[Complex A] y).X 0)) :
    PerfectDGHomotopyCategoryOver A (QuotientObject D S) Set.univ ≌
      CompletedTriaQuotient A D S :=
  localPerfectQuotientEquivalence A D S
    (allHomKFlat_local A D (allHomKFlat_of_flat_zero A D hz hf) S)

end SerrePositivity.DifferentialGraded.DGQuotient
