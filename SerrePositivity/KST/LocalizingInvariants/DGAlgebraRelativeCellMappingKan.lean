module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingFibration
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeMultiplicativeSimplices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanLimits
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces

/-!
概要：全射標的射の上で、cell 源と指定底を保つ実乗法的写像単体は Kan。
方針：元の全写像の Kan fibration の、指定底への元の pullback を使う。
規約：底射 s は元の代数射で、各単体次数で固定される。
使われ方：Postnikov 拡大の指定底上の導来比較の実相対模型。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open SSet.modelCategoryQuillen
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R)) {X B : Mon (Complex R)}
  (q : X ⟶ B) (hq : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations R q.hom)
  (s : cellResolution R A ⟶ B)

include hq

lemma relativeMultiplicativeCellMapping_kanComplex :
    SSet.KanComplex (relativeMultiplicativeMappingSimplices R q s) := by
  have := multiplicativeCellMapping_fibration R A q hq
  have : SSet.KanComplex (SSet.stdSimplex.obj (SimplexCategory.mk 0) : SSet.{u}) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointKanObject.isKanComplex
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.pullback_kanComplex_of_fibration
    (multiplicativeMappingPostcompose R (cellResolution R A) q) (multiplicativeMappingBase R s)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
