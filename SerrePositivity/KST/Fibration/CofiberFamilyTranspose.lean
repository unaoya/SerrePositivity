module
public import SerrePositivity.KST.Fibration.WeakStringCofiberVertices
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InternalHomFlipVertices

/-! # cofiber 図式の族の関手圏への転置

パラメーター付きの全 cofiber 四角形を関手圏の一つの実 cofiber 四角形に移す。
全高次自然変換を保持し、零角と押し出し性を点ごとの普遍性で証明する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
namespace SerrePositivity.KST.Fibration

/-- 交換した内部 Hom の族の評価は、元の関手頂点が表す図式そのもの。 -/
lemma flipFamily_evaluate {A K Y : SSet.{u}} (f : A ⟶ (ihom K).obj Y) (a : A _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A K Y f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K Y).symm (f.app (Opposite.op ⦋0⦌) a) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K A Y (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A K Y f) = f :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A K Y).symm_apply_apply f
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A K Y f) a
  rw [hi] at he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K Y).injective
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex _ = _
  rw [Equiv.apply_symm_apply]
  exact he.symm

/-- 全 cofiber 四角形の族を、同じ全パラメーターを持つ関手圏の四角形へ移す。 -/
def cofiberFamilySquare {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (p : A ⟶ cofiberDiagrams B.obj) :
    Δ[1] ⊗ Δ[1] ⟶ (ihom A).obj B.obj :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A (Δ[1] ⊗ Δ[1]) B.obj
    (p ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι)

/-- 転置した族を各点で評価すると、元の同じ実四角形を回収する。 -/
lemma cofiberFamilySquare_evaluate {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (p : A ⟶ cofiberDiagrams B.obj) (a : A _⦋0⦌) :
    cofiberFamilySquare p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (p.app (Opposite.op ⦋0⦌) a).val :=
  flipFamily_evaluate _ a

/-- 転置した族の底辺は、元の底辺の族の転置そのもの。 -/
lemma cofiberFamilySquare_bottom {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (p : A ⟶ cofiberDiagrams B.obj) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ cofiberFamilySquare p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A Δ[1] B.obj (p ≫ cofiberProjection B.obj) := by
  unfold cofiberFamilySquare
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A Δ[1] B.obj) (Category.assoc _ _ _)

/-- 族の零角は、関手圏でも実際に零対象である。 -/
lemma cofiberFamilySquare_zero {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (p : A ⟶ cofiberDiagrams B.obj) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (cofiberFamilySquare p) 0 1) := by
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((cofiberFamilySquare p).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1))
  rw [cofiberFamilySquare, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero]
  apply isZeroVertex_functorVertex_of_pointwise
  intro a
  have hz := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (p.app (Opposite.op ⦋0⦌) a)).1
  have he := cofiberVertex_corner B (p.app (Opposite.op ⦋0⦌) a)
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1)
  exact (congrArg _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex he).mpr hz

/-- パラメーター付き cofiber を関手圏の零角を持つ三角形として保持する。 -/
def cofiberFamilyZeroTriangle {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (p : A ⟶ cofiberDiagrams B.obj) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle ((ihom A).obj B.obj) :=
  ⟨cofiberFamilySquare p, cofiberFamilySquare_zero p⟩

/-- 転置した族は点ごとの普遍性から関手圏の実 cofiber 列である。 -/
lemma cofiberFamily_isCofiber {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}}
    (p : A ⟶ cofiberDiagrams B.obj) : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence (cofiberFamilyZeroTriangle p) := by
  apply (functor_zeroTriangle_pushout_iff (cofiberFamilyZeroTriangle p)).2
  intro a
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (cofiberFamilySquare p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a)
  rw [cofiberFamilySquare_evaluate]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (p.app (Opposite.op ⦋0⦌) a)).2

end SerrePositivity.KST.Fibration
