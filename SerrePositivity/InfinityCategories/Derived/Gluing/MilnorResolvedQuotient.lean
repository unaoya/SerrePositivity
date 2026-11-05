module
public import SerrePositivity.InfinityCategories.Derived.Gluing.MilnorDiagonalThickImage
public import SerrePositivity.InfinityCategories.Derived.DGQuotientExactFunctor
public import SerrePositivity.InfinityCategories.Derived.ResolvedDGQuotientZeroObjects
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet KST.SConstruction KST.LocalizingInvariants
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
abbrev dgGluingMilnorResolvedQuotientNerve :=
  resolvedDGQuotientNerve R (DGOdotGluing R d)
    (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)
def dgGluingMilnorResolvedQuotientFunctor :=
  resolvedDGQuotientFunctor R (DGOdotGluing R d)
    (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)
def dgGluingMilnorNativeDiagonalSource : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u + 1} where
  obj := dgNerve R (DGSmallPerfectBase R (dgAlgebraCategory R d.source))
  isQuasicategory := inferInstance
  isStable := dgSmallPerfectBaseNerve_isStable R (dgAlgebraCategory R d.source)
variable [IsDGPretriangulated R (DGOdotGluing R d)]
def dgGluingMilnorNativeMiddle : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u + 1} where
  obj := dgNerve R (DGOdotGluing R d)
  isQuasicategory := inferInstance
  isStable := dgNerve_isStable_of_pretriangulated R _
def dgGluingMilnorNativeResolvedQuotient : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u + 1} where
  obj := dgGluingMilnorResolvedQuotientNerve R d
  isQuasicategory := inferInstance
  isStable := resolvedDGQuotientNerve_isStable R (DGOdotGluing R d) _
def dgGluingMilnorResolvedProjection :
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingMilnorNativeMiddle R d) (dgGluingMilnorNativeResolvedQuotient R d) where
  hom := dgGluingMilnorResolvedQuotientFunctor R d
  isExact := resolvedDGQuotientFunctor_isExactFunctor R (DGOdotGluing R d) _
variable [IsExactFunctor (dgNerve.map (dgOdotQuotientInput R d).diagonal)]
def dgGluingMilnorNativeDiagonal :
    _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap (dgGluingMilnorNativeDiagonalSource R d) (dgGluingMilnorNativeMiddle R d) where
  hom := dgNerve.map (dgOdotQuotientInput R d).diagonal
  isExact := inferInstance
omit [IsDGPretriangulated R (DGOdotGluing R d)]
  [IsExactFunctor (dgNerve.map (dgOdotQuotientInput R d).diagonal)] in
lemma dgGluingMilnorResolvedQuotient_kills_diagonal
    (a : DGSmallPerfectBase R (dgAlgebraCategory R d.source)) :
    IsZeroVertex ((dgGluingMilnorResolvedQuotientFunctor R d).app (Opposite.op ⦋0⦌)
      (Simplex.vertex (A := R) ((dgOdotQuotientInput R d).diagonal.obj a))) := by
  exact resolvedDGQuotientFunctor_kills R (DGOdotGluing R d)
    (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)
    ⟨(dgOdotQuotientInput R d).diagonal.obj a, ⟨a, rfl⟩⟩
end SerrePositivity.InfinityCategories
