module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovRelativeMappingIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeCellMappingKan
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovHomotopyPullback

/-!
概要：元の Postnikov 上段と class の、指定底を保つ cell 写像模型はともに Kan。
方針：元の class の全射性を相対 Kan 判定に代入し、全単体の実同型で戻す。
規約：元の底射 b と、その零切断像を保持する。導来比較は入力にしない。
使われ方：Postnikov 拡大の固定底に相対的な普遍性の実模型側。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A B : Mon (Complex R)) [B.X.IsStrictlyLE 0]
  (n : ℤ) (hn : 0 ≤ n) (b : cellResolution R A ⟶ postnikov R B n)

lemma postnikovClassRelativeMultiplicativeCellMapping_kanComplex :
    SSet.KanComplex (relativeMultiplicativeMappingSimplices R (postnikovPerturbedClass R B n hn)
      (b ≫ SquareZero.zeroSection (postnikov R B n)
        (postnikovShiftedLayerBimodule R B n hn 1))) := by
  apply relativeMultiplicativeCellMapping_kanComplex R A
  have := postnikovPerturbedClass_epi R B n hn
  intro k
  exact (ModuleCat.epi_iff_surjective _).mp (inferInstance :
    Epi ((postnikovPerturbedClass R B n hn).hom.f k))

include hn in
lemma postnikovRelativeMultiplicativeCellMapping_kanComplex :
    SSet.KanComplex (relativeMultiplicativeMappingSimplices R
      (postnikovTransition R B (n + 1) n (by omega)) b) := by
  have := postnikovClassRelativeMultiplicativeCellMapping_kanComplex R A B n hn b
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso
    (postnikovRelativeMultiplicativeMappingIso R (cellResolution R A) B n hn b).symm

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
