module
public import SerrePositivity.KST.SConstruction.KIteratedTracedFamilyLifting
public import SerrePositivity.KST.SConstruction.KRawFamilyComparison

/-! # 同じ補正族の直接延長と段階的延長の実比較
概要：入れ子の全補正区間を持つ raw 族について、二つの BF 延長を境界固定で比較する。
方針：元の境界からの直接持ち上げと、中間族を固定した持ち上げの同じ射影を照合する。
規約：比較の全時刻で raw 族を固定し、元の BF 境界も固定する。
使われ方：共通面からの相対延長の順序の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet Spectra
open scoped Simplicial
variable (X Y : StableModel.{u}) {T U V : SSet.{u}}
  (j : T ⟶ U) [Mono j] (k : U ⟶ V) [Mono k]
  (f : ∀ n, V ⟶ (PointedObject.basedHom ((kOmegaSpectrum X).level n).space
    ((kKanSequence Y).level n).space).right)
  (H : ∀ n, SSet.Homotopy
    (f (n + 1) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre ((kOmegaSpectrum X).sigma n)
      ((kKanSequence Y).level (n + 1)).space)
    (f n ≫ RawSpectrumMapping.step (kOmegaSpectrum X) (kKanSequence Y) n))
  (B : TracedSequenceBoundaryData (kOmegaSpectrum X) (kKanSequence Y) j
    (fun n => k ≫ f n)
    (tracedSequenceBoundaryCompatibility (kOmegaSpectrum X) (kKanSequence Y) k f H))

/-- 同じ raw 族を、元の BF 境界から直接持ち上げる。 -/
def kDirectTracedFamilyLiftData :=
  kRelativeFamilyLiftData X Y (j ≫ k)
    (kTracedBoundaryLiftData X Y j (fun n => k ≫ f n)
      (tracedSequenceBoundaryCompatibility (kOmegaSpectrum X) (kKanSequence Y) k f H) B).val
    (prescribedSequenceFamilyRectification (kOmegaSpectrum X) (kKanSequence Y) k f H
      (extendedTracedSequenceBoundaryData (kOmegaSpectrum X) (kKanSequence Y) j k f H B))
    (by
      rw [Category.assoc, prescribedSequenceFamilyRectification_extension,
        prescribedSequenceFamilyRectification_boundary]
      exact (kTracedBoundaryLiftData X Y j (fun n => k ≫ f n)
        (tracedSequenceBoundaryCompatibility (kOmegaSpectrum X) (kKanSequence Y) k f H) B).property)

/-- 直接延長と中間族を固定した延長を、同じ元の境界上で固定して実比較する。 -/
def kIteratedTracedFamilyComparison :
    SSet.Homotopy (kIteratedTracedFamilyLiftData X Y j k f H B).val
      (kDirectTracedFamilyLiftData X Y j k f H B).val :=
  kRawFamilyComparison X Y (j ≫ k)
    (kIteratedTracedFamilyLiftData X Y j k f H B).val
    (kDirectTracedFamilyLiftData X Y j k f H B).val
    ((kIteratedTracedFamilyLiftData_projection X Y j k f H B).trans
      (kDirectTracedFamilyLiftData X Y j k f H B).property.2.symm)
    ((kIteratedTracedFamilyLiftData_boundary X Y j k f H B).trans
      (kDirectTracedFamilyLiftData X Y j k f H B).property.1.symm)

/-- 直接延長との比較の全時刻で、元の同じ raw 族を保つ。 -/
lemma kIteratedTracedFamilyComparison_projection :
    (kIteratedTracedFamilyComparison X Y j k f H B).h ≫ kRawMappingProjection X Y =
      fst V (Δ[1] : SSet.{u}) ≫
        prescribedSequenceFamilyRectification (kOmegaSpectrum X) (kKanSequence Y) k f H
          (extendedTracedSequenceBoundaryData (kOmegaSpectrum X) (kKanSequence Y) j k f H B) := by
  rw [kIteratedTracedFamilyComparison, kRawFamilyComparison_projection,
    kIteratedTracedFamilyLiftData_projection]

/-- 直接延長との比較は、元の同じ BF 境界上で定数である。 -/
lemma kIteratedTracedFamilyComparison_boundary :
    ((j ≫ k) ▷ (Δ[1] : SSet.{u})) ≫
      (kIteratedTracedFamilyComparison X Y j k f H B).h =
      fst T (Δ[1] : SSet.{u}) ≫
        (kTracedBoundaryLiftData X Y j (fun n => k ≫ f n)
          (tracedSequenceBoundaryCompatibility (kOmegaSpectrum X)
            (kKanSequence Y) k f H) B).val := by
  rw [kIteratedTracedFamilyComparison, kRawFamilyComparison_boundary,
    kIteratedTracedFamilyLiftData_boundary]

end SerrePositivity.KST.SConstruction
