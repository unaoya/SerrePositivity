module
public import SerrePositivity.KST.SConstruction.KTracedFamilyLifting
public import SerrePositivity.KST.SConstruction.TracedSequenceBoundaryExtension

/-! # 部分族の同じ BF 境界を保つ入れ子の延長
概要：一回目の BF 族を新しい境界として固定し、より大きいパラメータへ延長する。
方針：一回目の全補正区間を次の raw 境界へ移し、同じ BF 族から相対持ち上げする。
規約：中間の BF 族・元の境界・全 raw 射影を厳密に保持する。
使われ方：共通面を固定した多段の coherent 族の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet Spectra
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

/-- 既に構成した中間 BF 族を固定して、次のパラメータへ延長する。 -/
def kIteratedTracedFamilyLiftData :=
  kRelativeFamilyLiftData X Y k
    (kTracedFamilyLiftData X Y j (fun n => k ≫ f n)
      (tracedSequenceBoundaryCompatibility (kOmegaSpectrum X) (kKanSequence Y) k f H) B).val
    (prescribedSequenceFamilyRectification (kOmegaSpectrum X) (kKanSequence Y) k f H
      (extendedTracedSequenceBoundaryData (kOmegaSpectrum X) (kKanSequence Y) j k f H B))
    ((kTracedFamilyLiftData_projection X Y j (fun n => k ≫ f n)
      (tracedSequenceBoundaryCompatibility (kOmegaSpectrum X) (kKanSequence Y) k f H) B).trans
      (prescribedSequenceFamilyRectification_extension
        (kOmegaSpectrum X) (kKanSequence Y) j k f H B).symm)

/-- 延長した BF 族は、中間の同じ BF 族を厳密に回収する。 -/
lemma kIteratedTracedFamilyLiftData_intermediate :
    k ≫ (kIteratedTracedFamilyLiftData X Y j k f H B).val =
      (kTracedFamilyLiftData X Y j (fun n => k ≫ f n)
        (tracedSequenceBoundaryCompatibility (kOmegaSpectrum X) (kKanSequence Y) k f H) B).val :=
  (kIteratedTracedFamilyLiftData X Y j k f H B).property.1

/-- 合成した元の境界上でも、最初に選んだ同じ BF 境界を回収する。 -/
lemma kIteratedTracedFamilyLiftData_boundary :
    (j ≫ k) ≫ (kIteratedTracedFamilyLiftData X Y j k f H B).val =
      (kTracedBoundaryLiftData X Y j (fun n => k ≫ f n)
        (tracedSequenceBoundaryCompatibility (kOmegaSpectrum X) (kKanSequence Y) k f H) B).val := by
  rw [Category.assoc, kIteratedTracedFamilyLiftData_intermediate,
    kTracedFamilyLiftData_boundary]

/-- 延長の射影は、中間の補正全区間を指定した同じ raw 厳密化である。 -/
lemma kIteratedTracedFamilyLiftData_projection :
    (kIteratedTracedFamilyLiftData X Y j k f H B).val ≫ kRawMappingProjection X Y =
      prescribedSequenceFamilyRectification (kOmegaSpectrum X) (kKanSequence Y) k f H
        (extendedTracedSequenceBoundaryData (kOmegaSpectrum X) (kKanSequence Y) j k f H B) :=
  (kIteratedTracedFamilyLiftData X Y j k f H B).property.2

end SerrePositivity.KST.SConstruction
