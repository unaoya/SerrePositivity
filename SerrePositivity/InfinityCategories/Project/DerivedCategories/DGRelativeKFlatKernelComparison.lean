module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DeformationFunctorDescent
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatKernelToDerived
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRelativeKFlatKernelNerve
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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded SSet
variable (R : Type u) [CommRing R] (D E : Type v)
  [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D] [_root_.SerrePositivity.DifferentialGraded.DGCategory R E] [Small.{u} E]
/-- 同じ実 augmentation から得る、K-flat 入力上の任意 kernel の指定導来比較。 -/
def dgRelativeKFlatKernelComparisonIso (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelToDerived R D E P) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity_relativeKFlatRestrictionIso R D E P).precomp
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D) ≪≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.deformationFunctorDescentIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgSemifreeToRelativeKFlatNerve R D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatQuasiIsomorphismEdges R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolutionAugmentationHomotopy_vertex_mem R D)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelToDerived R D E P)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelToDerived_invertsQuasiIsomorphismEdges R D E P)
/-- K-flat kernel の通常全単体作用に出力分解を続けると、同じ通常 tensor の作用になる。 -/
lemma dgRelativeKFlatKernelNerve_resolution (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelToDerived R D E P := by
  simp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve_inclusion, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelToDerived]
/-- 右相対 K-flat kernel の元の指定導来作用を、通常の K-flat 全単体作用へ比較する。 -/
def dgRelativeKFlatKernelNerve_derivedIso (P : _root_.SerrePositivity.DifferentialGraded.Bimodule R E D)
    (hP : _root_.SerrePositivity.DifferentialGraded.Bimodule.rightRelativeKFlat R E D P) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R D ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKernelDerivedInfinity R D E P)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatKernelNerve R D E P hP ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRelativeKFlatResolution R E) := by
  rw [dgRelativeKFlatKernelNerve_resolution]
  exact dgRelativeKFlatKernelComparisonIso R D E P
end SerrePositivity.InfinityCategories.Project.DerivedCategories
