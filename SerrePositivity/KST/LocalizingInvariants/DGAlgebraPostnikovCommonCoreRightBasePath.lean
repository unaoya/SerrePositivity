module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenWitness
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightClassWitness
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellPathNonpositive
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathDiscreteTarget

/-!
概要：元の指定右経路を、非正次数共通源上の二つの標準 cell class の実経路へ移す。
方針：cell 比較への経路反映と実 class の後合成を使い、零底への像を定数経路と照合する。
規約：元の経路を入力とし、共通源の全射準同型性を保持。使われ方：class 比較の貼合せ。
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
  (d : PostnikovCommonLayerInverse R hn f c)

attribute [local instance] PostnikovRoofZeroSpan.refined_source_nonpositive
  PostnikovRoofZeroSpan.refined_target_nonpositive

local instance commonBasePath_apex_nonpositive :
    (postnikovCommonClassBase R hn f c d).X.IsStrictlyLE 0 :=
  (roofRefine R hn f c d.zero.source_le).roof_nonpositive
local instance commonBasePath_target_lowerBound :
    (postnikov R (B.obj i).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj i).obj 0

def postnikovCommonRightBasePath : Path.Witness R (postnikovCommonRightBase R hn f c d)
    (postnikovCommonRightDenBase R hn f c d) :=
  (roofRefine R hn f c d.zero.source_le).rightPath

lemma postnikovCommonRightBasePath_zero : (postnikovCommonRightBasePath R hn f c d).hom ≫
    Path.map R (postnikovTransition R (B.obj i).obj n 0 (by omega)) =
    (postnikovCommonRightBase R hn f c d ≫ postnikovTransition R (B.obj i).obj n 0 (by omega)) ≫
      Path.diagonal R (postnikov R (B.obj i).obj 0) :=
  Path.Witness.hom_eq_constant R ((postnikovCommonRightBasePath R hn f c d).postcomp
    (postnikovTransition R (B.obj i).obj n 0 (by omega)))

abbrev postnikovCommonRightCellSource :=
  cellPathNonpositiveSource R (postnikovCommonClassBase R hn f c d)

def postnikovCommonRightCellProjection : postnikovCommonRightCellSource R hn f c d ⟶
    postnikovCommonClassBase R hn f c d := cellPathNonpositiveProjection R _

lemma postnikovCommonRightCellProjection_quasiIso :
    QuasiIso (postnikovCommonRightCellProjection R hn f c d).hom :=
  cellPathNonpositiveProjection_quasiIso R _ (by
    change (postnikovCommonClassBase R hn f c d).X.IsLE 0
    infer_instance)

lemma postnikovCommonRightCellProjection_surjective (degree : ℤ) :
    Function.Surjective ((postnikovCommonRightCellProjection R hn f c d).hom.f degree) :=
  cellPathNonpositiveProjection_surjective R _ degree

def postnikovCommonRightCellClassWitness : Path.Witness R
    (cellPathNonpositiveComparison R (postnikovCommonRightBase R hn f c d) ≫
      postnikovCellClass R (B.obj i).obj n hn)
    (cellPathNonpositiveComparison R (postnikovCommonRightDenBase R hn f c d) ≫
      postnikovCellClass R (B.obj i).obj n hn) :=
  (cellPathNonpositiveWitness R (postnikovCommonRightBasePath R hn f c d)).postcomp
    (postnikovCellClass R (B.obj i).obj n hn)

lemma postnikovCommonRightCellClassWitness_zero :
    (postnikovCommonRightCellClassWitness R hn f c d).hom ≫
      Path.map R (SquareZero.projection (postnikov R (B.obj i).obj n)
        (postnikovShiftedLayerBimodule R (B.obj i).obj n hn 1) ≫
          postnikovTransition R (B.obj i).obj n 0 (by omega)) =
    (postnikovCommonRightCellProjection R hn f c d ≫ postnikovCommonRightBase R hn f c d ≫
      postnikovTransition R (B.obj i).obj n 0 (by omega)) ≫
        Path.diagonal R (postnikov R (B.obj i).obj 0) := by
  let q := SquareZero.projection (postnikov R (B.obj i).obj n)
    (postnikovShiftedLayerBimodule R (B.obj i).obj n hn 1) ≫
      postnikovTransition R (B.obj i).obj n 0 (by omega)
  have h := Path.Witness.hom_eq_constant R
    ((postnikovCommonRightCellClassWitness R hn f c d).postcomp q)
  have he : (cellPathNonpositiveComparison R (postnikovCommonRightBase R hn f c d) ≫
      postnikovCellClass R (B.obj i).obj n hn) ≫ q =
      postnikovCommonRightCellProjection R hn f c d ≫ postnikovCommonRightBase R hn f c d ≫
        postnikovTransition R (B.obj i).obj n 0 (by omega) := by
    simp only [q, Category.assoc]
    rw [reassoc_of% (postnikovCellClass_projection R (B.obj i).obj n hn),
      reassoc_of% (cellPathNonpositiveComparison_projection R (postnikovCommonRightBase R hn f c d))]
    rfl
  exact h.trans (congrArg (fun t => t ≫ Path.diagonal R (postnikov R (B.obj i).obj 0)) he)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovCommonCore
