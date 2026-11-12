module
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFStepOmega
public import SerrePositivity.KST.SConstruction.DGKappaNativeBFStructureNaturality
public import SerrePositivity.KST.Spectra.KanSequence

/-!
概要：同じ未完備 native 一四角形の有限入力上で、実 BF Ω スペクトルを構成する。
方針：元の零段と全実正段、単射構造射、証明済みの全 Ω 条件を束ねる。
規約：全 Hom 作用を段関手に保持。使われ方：同じ四辺と二胞体の厳密豊穣スペクトル化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories
open NonConnective Spectra
variable (R : Type u) [CommRing R] (D : PerfDGInput.{u, max (u + 1) v} R)
  {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

/-- 概要：同じ零段 ΩB₀ と全実正段の厳密豊穣関手族。
方針：構成済みの実再帰段を同じ番号に並べる。
規約：同じ有限入力に限定。使われ方：全 BF 段の Hom 作用。 -/
def dgKappaNativeBFFiniteLevelFunctor : (n : ℕ) →
    EnrichedFunctor SSet.{max (u + 1) v} (DGKappaNativeBFFiniteInput.{u, v} R D I)
      PointedSSetObject.{max (u + 1) v}
  | 0 => dgKappaNativeBFFiniteZeroFunctor.{u, v} R D I
  | n + 1 => (dgKappaNativeBFFinitePositiveStage.{u, v} R D I n).functor

/-- 概要：同じ全実段の元の suspension 構造射。
方針：最初の実単射置換と、実際の前段からの同じ円柱比較を使う。
規約：元の構造射を保持。使われ方：実 BF Kan 列の構造射。 -/
def dgKappaNativeBFFiniteStructureMap : (n : ℕ) →
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) →
    ((dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).comp SSet
      (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v})).obj C ⟶
        (dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I (n + 1)).obj C
  | 0, C => dgKappaNativeBFFiniteFirstStructureMap.{u, v} R D I C
  | n + 1, C => dgKappaNativeBFFiniteStepStructureMap.{u, v} R D I n
      (dgKappaNativeBFFinitePositiveStage.{u, v} R D I n) C

/-- 概要：同じ全実段の Kan 性。
方針：元の零段と実再帰段の Kan 性を使う。
規約：追加仮定なし。使われ方：実 BF Kan 列の全値。 -/
lemma dgKappaNativeBFFiniteLevel_kanComplex (n : ℕ)
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanComplex (((dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).obj C).obj).right := by
  cases n with
  | zero => exact dgKappaNativeBFFiniteZero_kanComplex.{u, v} R D I C
  | succ n => exact (dgKappaNativeBFFinitePositiveStage.{u, v} R D I n).kan C

/-- 概要：同じ全実構造射の基礎単射性。
方針：最初の単射置換と正の実次段比較の単射性を使う。
規約：実際の前段からの構造射。使われ方：実 BF 条件。 -/
lemma dgKappaNativeBFFiniteStructureMap_mono (n : ℕ)
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    Mono (show _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension
      (((dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).obj C).obj) ⟶
        ((dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I (n + 1)).obj C).obj from
          dgKappaNativeBFFiniteStructureMap.{u, v} R D I n C).right := by
  cases n with
  | zero => exact dgKappaNativeBFFiniteFirstStructureMap_mono.{u, v} R D I C
  | succ n =>
    exact dgKappaNativeBFFiniteStepStructureMap_mono.{u, v} R D I n
      (dgKappaNativeBFFinitePositiveStage.{u, v} R D I n) C

/-- 概要：同じ全構造射は有限入力の全 Hom に厳密に自然。
方針：元の最初の変換と同じ正の実構造変換を使う。
規約：元の二胞体を保持。使われ方：全 BF 写像空間への Hom 作用。 -/
lemma dgKappaNativeBFFiniteStructureMap_whisker (n : ℕ)
    (C E : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    ((dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).comp SSet
        (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v})).map C E ≫
        eHomWhiskerLeft SSet
          (((dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).comp SSet
            (pointedTensorEnrichedFunctor PointedSimplicialSet.circle.{max (u + 1) v})).obj C)
          (dgKappaNativeBFFiniteStructureMap.{u, v} R D I n E) =
      (dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I (n + 1)).map C E ≫
        eHomWhiskerRight SSet (dgKappaNativeBFFiniteStructureMap.{u, v} R D I n C)
          ((dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I (n + 1)).obj E) := by
  cases n with
  | zero => exact dgKappaNativeBFFiniteFirstStructureMap_whisker.{u, v} R D I C E
  | succ n =>
    exact dgKappaNativeBFFiniteStepStructureMap_whisker.{u, v} R D I n
      (dgKappaNativeBFFinitePositiveStage.{u, v} R D I n) C E

/-- 概要：同じ零段・全正段・全単射構造射を持つ実 Kan 列。
方針：同じ実段と構造射を元の Kan 列へ束ねる。
規約：値と構造射を選び直さない。使われ方：同じ実 Ω スペクトルの基礎列。 -/
def dgKappaNativeBFFiniteKanSequence (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    KanSequence.{max (u + 1) v} where
  level n := ⟨((dgKappaNativeBFFiniteLevelFunctor.{u, v} R D I n).obj C).obj,
    dgKappaNativeBFFiniteLevel_kanComplex.{u, v} R D I n C⟩
  sigma n := dgKappaNativeBFFiniteStructureMap.{u, v} R D I n C

/-- 概要：同じ実 Kan 列の全構造随伴は Ω 条件を満たす。
方針：構成済みの最初の Ω 条件と正の実次段の Ω 条件を使う。
規約：Ω 条件の仮定なし。使われ方：元の有限 BF Ω スペクトル。 -/
lemma dgKappaNativeBFFiniteKanSequence_omegaCondition
    (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    (dgKappaNativeBFFiniteKanSequence.{u, v} R D I C).OmegaCondition := by
  intro n
  cases n with
  | zero => exact dgKappaNativeBFFiniteFirstStructureAdjoint_piIsomorphism.{u, v} R D I C
  | succ n =>
    exact dgKappaNativeBFFiniteStepStructureAdjoint_piIsomorphism.{u, v} R D I n
      (dgKappaNativeBFFinitePositiveStage.{u, v} R D I n) C

/-- 概要：同じ未完備 native 四頂点像上の実 BF Ω スペクトル。
方針：全単射構造射と証明済みの全 Ω 条件を同じ実列へ束ねる。
規約：一般安定圏の BF 関手は構成しない。使われ方：同じ実四角形の全スペクトル像。 -/
def dgKappaNativeBFFiniteOmegaSpectrum (C : DGKappaNativeBFFiniteInput.{u, v} R D I) :
    OmegaSpectrum.{max (u + 1) v} :=
  (dgKappaNativeBFFiniteKanSequence.{u, v} R D I C).toOmegaSpectrum
    (fun n => dgKappaNativeBFFiniteStructureMap_mono.{u, v} R D I n C)
    (dgKappaNativeBFFiniteKanSequence_omegaCondition.{u, v} R D I C)

end SerrePositivity.KST.SConstruction
