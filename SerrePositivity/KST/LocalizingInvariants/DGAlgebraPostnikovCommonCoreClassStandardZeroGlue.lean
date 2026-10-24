module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassStandard

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
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} (hn : 0 ≤ n)
  {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (lowerFunctor R n hn)) i m hi)
  (d : PostnikovCommonLayerInverse R hn f c) {j : ℕ} {hj : j ≤ i}
  (e : PostnikovZeroLayerInverse R n f j i hj)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

abbrev postnikovCommonClassStandardGlueSource :=
  cellPathNonpositiveSource R (postnikovCommonRightZeroGlueSource R hn f c d)

def postnikovCommonClassStandardGlueProjection :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d) ≫
    postnikovCommonRightZeroGlueProjection R hn f c d

lemma postnikovCommonClassStandardGlueProjection_quasiIso :
    QuasiIso (postnikovCommonClassStandardGlueProjection R hn f c d).hom :=
  quasiIso_comp _ _ (hφ := cellPathNonpositiveProjection_quasiIso R _ (by
    change (postnikovCommonRightZeroGlueSource R hn f c d).X.IsLE 0
    infer_instance)) (hφ' := postnikovCommonRightZeroGlueProjection_quasiIso R hn f c d)

lemma postnikovCommonClassStandardGlueProjection_surjective (degree : ℤ) :
    Function.Surjective ((postnikovCommonClassStandardGlueProjection R hn f c d).hom.f degree) :=
  (postnikovCommonRightZeroGlueProjection_surjective R hn f c d degree).comp
    (cellPathNonpositiveProjection_surjective R (postnikovCommonRightZeroGlueSource R hn f c d) degree)

def postnikovCommonClassStandardGlueLeft :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d) ≫
    postnikovCommonClassTransitionSource R hn f c d (hj := hj)

def postnikovCommonClassStandardGlueRight :=
  cellPathNonpositiveProjection R (postnikovCommonRightZeroGlueSource R hn f c d) ≫
    postnikovCommonClassStandardEndpoint R hn f c d hj

lemma postnikovCommonClassStandardGlueLeft_projection :
    postnikovCommonClassStandardGlueLeft R hn f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonClassStandardGlueProjection R hn f c d := by
  rw [postnikovCommonClassStandardGlueLeft, Category.assoc,
    postnikovCommonClassTransitionSource_projection]
  rfl

lemma postnikovCommonClassStandardGlueRight_projection :
    postnikovCommonClassStandardGlueRight R hn f c d (hj := hj) ≫ SquareZero.projection _ _ =
      postnikovCommonClassStandardGlueProjection R hn f c d := by
  rw [postnikovCommonClassStandardGlueRight, Category.assoc,
    postnikovCommonClassStandardEndpoint_projection]
  rfl

def postnikovCommonClassStandardZeroGlueWitness : Path.Witness R
    (postnikovCommonClassStandardGlueLeft R hn f c d (hj := hj) ≫
      postnikovCommonClassTransitionToZero R hn f c d hj)
    (postnikovCommonClassStandardGlueRight R hn f c d (hj := hj) ≫
      postnikovCommonClassTransitionToZero R hn f c d hj) := by
  let z := postnikovCommonClassTransitionToZero R hn f c d hj
  let w := (((postnikovCommonClassTransitionWitness R hn f c d e).postcomp z).cellReverse R).cellComp R
    (((postnikovCommonClassStandardWitness R hn f c d hj).postcomp z).precomp
      (cellAugmentation R (postnikovCommonRightZeroGlueSource R hn f c d)))
  let v := w.precompNonpositiveDouble R
  exact ⟨v.hom, v.source_eq.trans (Category.assoc _ _ _).symm,
    v.target_eq.trans (Category.assoc _ _ _).symm⟩

lemma postnikovCommonClassStandardZeroGlueWitness_projection :
    (postnikovCommonClassStandardZeroGlueWitness R hn f c d e).hom ≫
      Path.map R (SquareZero.projection _ _) =
        (postnikovCommonClassStandardGlueProjection R hn f c d ≫
          (postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
            postnikovTransition R (A.obj j).obj n 0 (by omega))) ≫
              Path.diagonal R (postnikov R (A.obj j).obj 0) := by
  have : (postnikov R (A.obj j).obj 0).X.IsStrictlyGE 0 := by
    simpa only [neg_zero] using postnikov_lowerBound R (A.obj j).obj 0
  have hp : (postnikovCommonClassStandardGlueLeft R hn f c d (hj := hj) ≫
      postnikovCommonClassTransitionToZero R hn f c d hj) ≫ SquareZero.projection _ _ =
    postnikovCommonClassStandardGlueProjection R hn f c d ≫
      (postnikovCommonClassRetractBase R hn f c d (hj := hj) ≫
        postnikovTransition R (A.obj j).obj n 0 (by omega)) := by
    rw [Category.assoc, postnikovCommonClassTransitionToZero_projection,
      ← Category.assoc, postnikovCommonClassStandardGlueLeft_projection]
  exact (Path.Witness.hom_eq_constant R
    ((postnikovCommonClassStandardZeroGlueWitness R hn f c d e).postcomp
      (SquareZero.projection _ _))).trans (congrArg (fun t => t ≫
        Path.diagonal R (postnikov R (A.obj j).obj 0)) hp)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
