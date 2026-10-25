module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackConeEquiv
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeHomotopyPullbackExt
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeExtension

/-!
概要：底の定数経路を保つ平方零 class の零化錐を、既存の相対模型で表現する。
方針：全経路付き錐の部分型を用い、相対 lift の三成分と一意性を往復させる。
規約：元の底射影の全経路を型に保持する。導来写像空間の同値性を入力しない。
使われ方：Postnikov cell class の零化と、同じ底の Postnikov 拡大の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
open DGAlgebra DGAlgebra.HomotopyPullbackModel
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} (N : Bimod A A)
  (a : W ⟶ SquareZero.algebra A N) (T : Mon (Complex R))

abbrev RelativePathCone := {s : PathCone R a (SquareZero.zeroSection A N) T //
  s.path ≫ DGAlgebra.Path.map R (SquareZero.projection A N) =
    s.left ≫ a ≫ SquareZero.projection A N ≫ DGAlgebra.Path.diagonal R A}

def relativeHomPathCone (u : T ⟶ relativeModel N a) : RelativePathCone N a T :=
  ⟨{
    left := u ≫ relativeLeft N a
    right := u ≫ relativeRight N a
    path := u ≫ relativePath N a
    source_eq := by
      simpa only [relativePath, relativeLeft, Category.assoc] using congrArg (u ≫ ·)
        (RelativeHomotopyPullback.path_source R (SquareZero.projection A N) a
          (SquareZero.zeroSection A N))
    target_eq := by
      simpa only [relativePath, relativeRight, Category.assoc] using congrArg (u ≫ ·)
        (RelativeHomotopyPullback.path_target R (SquareZero.projection A N) a
          (SquareZero.zeroSection A N))
  }, by
    change (u ≫ relativePath N a) ≫ _ = (u ≫ relativeLeft N a) ≫ _
    rw [Category.assoc, relativePath_base]
    simp only [Category.assoc]⟩

def relativePathConeLift (s : RelativePathCone N a T) : T ⟶ relativeModel N a :=
  RelativeHomotopyPullback.lift R (SquareZero.projection A N) a (SquareZero.zeroSection A N)
    s.val.left s.val.right (s.val.witness R a (SquareZero.zeroSection A N))
    (by simpa only [PathCone.witness, Category.assoc] using s.property)

@[simp]
lemma relativePathConeLift_left (s : RelativePathCone N a T) :
    relativePathConeLift N a T s ≫ relativeLeft N a = s.val.left :=
  RelativeHomotopyPullback.lift_left R _ _ _ _ _ _ _

@[simp]
lemma relativePathConeLift_right (s : RelativePathCone N a T) :
    relativePathConeLift N a T s ≫ relativeRight N a = s.val.right :=
  RelativeHomotopyPullback.lift_right R _ _ _ _ _ _ _

@[simp]
lemma relativePathConeLift_path (s : RelativePathCone N a T) :
    relativePathConeLift N a T s ≫ relativePath N a = s.val.path :=
  RelativeHomotopyPullback.lift_path R _ _ _ _ _ _ _

def relativeHomPathConeEquiv : (T ⟶ relativeModel N a) ≃ RelativePathCone N a T where
  toFun := relativeHomPathCone N a T
  invFun := relativePathConeLift N a T
  left_inv u := by
    apply RelativeHomotopyPullback.hom_ext R (SquareZero.projection A N) a
      (SquareZero.zeroSection A N)
    · simpa only [relativeHomPathCone, relativeLeft, relativeRight, relativePath] using
        relativePathConeLift_left N a T (relativeHomPathCone N a T u)
    · simpa only [relativeHomPathCone, relativeLeft, relativeRight, relativePath] using
        relativePathConeLift_right N a T (relativeHomPathCone N a T u)
    · simpa only [relativeHomPathCone, relativeLeft, relativeRight, relativePath] using
        relativePathConeLift_path N a T (relativeHomPathCone N a T u)
  right_inv s := by
    apply Subtype.ext
    apply PathCone.ext R a (SquareZero.zeroSection A N)
    · simpa only [relativeHomPathCone] using relativePathConeLift_left N a T s
    · simpa only [relativeHomPathCone] using relativePathConeLift_right N a T s
    · simpa only [relativeHomPathCone] using relativePathConeLift_path N a T s

lemma relativeHomPathCone_comparison (u : T ⟶ relativeModel N a) :
    homPathCone R a (SquareZero.zeroSection A N) (u ≫ relativeComparison N a) =
      (relativeHomPathCone N a T u).val := by
  apply PathCone.ext R a (SquareZero.zeroSection A N)
  all_goals dsimp only [homPathCone, relativeHomPathCone]
  · change (u ≫ relativeComparison N a) ≫ left R _ _ = u ≫ relativeLeft N a
    rw [Category.assoc, relativeComparison_left]
  · change (u ≫ relativeComparison N a) ≫ right R _ _ = u ≫ relativeRight N a
    rw [Category.assoc, relativeComparison_right]
  · change (u ≫ relativeComparison N a) ≫ path R _ _ = u ≫ relativePath N a
    rw [Category.assoc, relativeComparison_path]

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
