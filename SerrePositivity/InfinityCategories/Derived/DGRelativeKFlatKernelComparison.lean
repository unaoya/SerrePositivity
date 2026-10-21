module
public import SerrePositivity.InfinityCategories.Derived.DeformationFunctorDescent
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelToDerived
public import SerrePositivity.InfinityCategories.Derived.DGRelativeKFlatKernelNerve
/-!
概要：K-flat 入力上で、元の指定導来 kernel と通常 tensor の指定出力分解を比較する。
方針：半自由包含上の同じ因数分解同型と、実 augmentation の降下比較を合成する。
規約：元の指定導来作用を保持する。使われ方：合成子と通常 tensor の結合子の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [DGCategory R D] [Small.{u} D] [DGCategory R E] [Small.{u} E]
/-- 同じ実 augmentation から得る、K-flat 入力上の任意 kernel の指定導来比較。 -/
def dgRelativeKFlatKernelComparisonIso (P : Bimodule R E D) :
    FunctorIso (dgRelativeKFlatResolution R D ≫ dgKernelDerivedInfinity R D E P)
      (dgRelativeKFlatKernelToDerived R D E P) :=
  (dgKernelDerivedInfinity_relativeKFlatRestrictionIso R D E P).precomp
    (dgRelativeKFlatResolution R D) ≪≫
      deformationFunctorDescentIso (dgRelativeKFlatResolution R D)
        (dgSemifreeToRelativeKFlatNerve R D) (dgRelativeKFlatQuasiIsomorphismEdges R D)
        (dgRelativeKFlatResolutionAugmentationHomotopy R D)
        (dgRelativeKFlatResolutionAugmentationHomotopy_vertex_mem R D)
        (dgRelativeKFlatKernelToDerived R D E P)
        (dgRelativeKFlatKernelToDerived_invertsQuasiIsomorphismEdges R D E P)
/-- K-flat kernel の通常全単体作用に出力分解を続けると、同じ通常 tensor の作用になる。 -/
lemma dgRelativeKFlatKernelNerve_resolution (P : Bimodule R E D)
    (hP : Bimodule.rightRelativeKFlat R E D P) :
    dgRelativeKFlatKernelNerve R D E P hP ≫ dgRelativeKFlatResolution R E =
      dgRelativeKFlatKernelToDerived R D E P := by
  simp only [dgRelativeKFlatResolution, ← Category.assoc,
    dgRelativeKFlatKernelNerve_inclusion, dgRelativeKFlatKernelToDerived]
/-- 右相対 K-flat kernel の元の指定導来作用を、通常の K-flat 全単体作用へ比較する。 -/
def dgRelativeKFlatKernelNerve_derivedIso (P : Bimodule R E D)
    (hP : Bimodule.rightRelativeKFlat R E D P) :
    FunctorIso (dgRelativeKFlatResolution R D ≫ dgKernelDerivedInfinity R D E P)
      (dgRelativeKFlatKernelNerve R D E P hP ≫ dgRelativeKFlatResolution R E) := by
  rw [dgRelativeKFlatKernelNerve_resolution]
  exact dgRelativeKFlatKernelComparisonIso R D E P
end SerrePositivity.InfinityCategories
