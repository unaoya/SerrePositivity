module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorDiagonalThickImage
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGQuotientExactFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ResolvedDGQuotientZeroObjects
/-!
概要：元の Milnor 対角像を消す同じ cell 平坦商と、元対角を二つの完全射として固定する。
方針：D-9 の実分解後の商を同じ対角像集合へ適用する。
規約：未分解 path 商への比較は要求せず、D-18 の前三角性の接続は明示する。
使われ方：K-S• の射影付け替えに渡す実 Verdier 列の二射。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded SSet KST.SConstruction KST.LocalizingInvariants
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
abbrev dgGluingMilnorResolvedQuotientNerve :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve R (DGOdotGluing R d)
    (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)
def dgGluingMilnorResolvedQuotientFunctor :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor R (DGOdotGluing R d)
    (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)
def dgGluingMilnorNativeDiagonalSource : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u + 1} where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source))
  isQuasicategory := inferInstance
  isStable := dgSmallPerfectBaseNerve_isStable R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source)
variable [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d)]
def dgGluingMilnorNativeMiddle : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u + 1} where
  obj := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (DGOdotGluing R d)
  isQuasicategory := inferInstance
  isStable := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerve_isStable_of_pretriangulated R _
def dgGluingMilnorNativeResolvedQuotient : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u + 1} where
  obj := dgGluingMilnorResolvedQuotientNerve R d
  isQuasicategory := inferInstance
  isStable := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientNerve_isStable R (DGOdotGluing R d) _
def dgGluingMilnorResolvedProjection :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgGluingMilnorNativeMiddle R d) (dgGluingMilnorNativeResolvedQuotient R d) where
  hom := dgGluingMilnorResolvedQuotientFunctor R d
  isExact := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_isExactFunctor R (DGOdotGluing R d) _
variable [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal)]
def dgGluingMilnorNativeDiagonal :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap (dgGluingMilnorNativeDiagonalSource R d) (dgGluingMilnorNativeMiddle R d) where
  hom := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal
  isExact := inferInstance
omit [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R (DGOdotGluing R d)]
  [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (dgOdotQuotientInput R d).diagonal)] in
lemma dgGluingMilnorResolvedQuotient_kills_diagonal
    (a : DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.source)) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((dgGluingMilnorResolvedQuotientFunctor R d).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (A := R) ((dgOdotQuotientInput R d).diagonal.obj a))) := by
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientFunctor_kills R (DGOdotGluing R d)
    (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)
    ⟨(dgOdotQuotientInput R d).diagonal.obj a, ⟨a, rfl⟩⟩
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
