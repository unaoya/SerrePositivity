module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassStandard

/-!
概要：遷移後の係数像と A の標準 class の二経路を、同じ非正次数共通源上で貼り合わせる。
方針：零標的へ移して反転・合成し、次数零の底への経路は定数であることを用いる。
規約：元の P への各次数全射準同型を保持。使われ方：標準 class への実相対比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R 1 f j i hj)

abbrev postnikovCommonClassStandardGlueSource :=
  cellPathNonpositiveSource R (postnikovCommonRightZeroGlueSource R f c d)

def postnikovCommonClassStandardGlueProjection :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R f c d) ≫
    postnikovCommonRightZeroGlueProjection R f c d

lemma postnikovCommonClassStandardGlueProjection_quasiIso :
    QuasiIso (postnikovCommonClassStandardGlueProjection R f c d).hom :=
  quasiIso_comp _ _ (hφ := cellPathNonpositiveProjection_quasiIso R _ (by
    change (postnikovCommonRightZeroGlueSource R f c d).X.IsLE 0
    infer_instance)) (hφ' := postnikovCommonRightZeroGlueProjection_quasiIso R f c d)

lemma postnikovCommonClassStandardGlueProjection_surjective (n : ℤ) :
    Function.Surjective ((postnikovCommonClassStandardGlueProjection R f c d).hom.f n) :=
  (postnikovCommonRightZeroGlueProjection_surjective R f c d n).comp
    (cellPathNonpositiveProjection_surjective R (postnikovCommonRightZeroGlueSource R f c d) n)

def postnikovCommonClassStandardGlueLeft :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R f c d) ≫
    postnikovCommonClassTransitionSource R f c d (hj := hj)

def postnikovCommonClassStandardGlueRight :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R f c d) ≫
    postnikovCommonClassStandardEndpoint R f c d hj

lemma postnikovCommonClassStandardGlueLeft_projection :
    postnikovCommonClassStandardGlueLeft R f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonClassStandardGlueProjection R f c d := by
  rw [postnikovCommonClassStandardGlueLeft, Category.assoc,
    postnikovCommonClassTransitionSource_projection]
  rfl

lemma postnikovCommonClassStandardGlueRight_projection :
    postnikovCommonClassStandardGlueRight R f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonClassStandardGlueProjection R f c d := by
  rw [postnikovCommonClassStandardGlueRight, Category.assoc,
    postnikovCommonClassStandardEndpoint_projection]
  rfl

def postnikovCommonClassStandardZeroGlueWitness : Path.Witness R
    (postnikovCommonClassStandardGlueLeft R f c d (hj := hj) ≫
      postnikovCommonClassTransitionToZero R f c d hj)
    (postnikovCommonClassStandardGlueRight R f c d (hj := hj) ≫
      postnikovCommonClassTransitionToZero R f c d hj) := by
  let z := postnikovCommonClassTransitionToZero R f c d hj
  let w := (((postnikovCommonClassTransitionWitness R f c d e).postcomp z).cellReverse R).cellComp R
    (((postnikovCommonClassStandardWitness R f c d hj).postcomp z).precomp
      (cellAugmentation R (postnikovCommonRightZeroGlueSource R f c d)))
  let v := w.precompNonpositiveDouble R
  exact ⟨v.hom, v.source_eq.trans (Category.assoc _ _ _).symm,
    v.target_eq.trans (Category.assoc _ _ _).symm⟩

lemma postnikovCommonClassStandardZeroGlueWitness_projection :
    (postnikovCommonClassStandardZeroGlueWitness R f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) =
        (postnikovCommonClassStandardGlueProjection R f c d ≫
          (postnikovCommonClassRetractBase R f c d (hj := hj) ≫
            postnikovTransition R (A.obj j).obj 1 0 (by omega))) ≫
              Path.diagonal R (postnikov R (A.obj j).obj 0) := by
  have : (postnikov R (A.obj j).obj 0).X.IsStrictlyGE 0 := by
    simpa only [neg_zero] using postnikov_lowerBound R (A.obj j).obj 0
  have hp : (postnikovCommonClassStandardGlueLeft R f c d (hj := hj) ≫
      postnikovCommonClassTransitionToZero R f c d hj) ≫ SquareZero.projection _ _ =
    postnikovCommonClassStandardGlueProjection R f c d ≫
      (postnikovCommonClassRetractBase R f c d (hj := hj) ≫
        postnikovTransition R (A.obj j).obj 1 0 (by omega)) := by
    rw [Category.assoc, postnikovCommonClassTransitionToZero_projection,
      ← Category.assoc, postnikovCommonClassStandardGlueLeft_projection]
  exact (Path.Witness.hom_eq_constant R
    ((postnikovCommonClassStandardZeroGlueWitness R f c d e).postcomp
      (SquareZero.projection _ _))).trans (congrArg (fun t => t ≫
        Path.diagonal R (postnikov R (A.obj j).obj 0)) hp)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
