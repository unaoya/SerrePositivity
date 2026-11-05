module
public import SerrePositivity.KST.Fibration.WeakStringCofiberVertices
public import SerrePositivity.InfinityCategories.Core.InternalHomFlipVertices

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
    internalHomFlipHomEquiv A K Y f ≫ evaluateFunctorAt a =
      (functorVertexEquiv K Y).symm (f.app (Opposite.op ⦋0⦌) a) := by
  have hi : internalHomFlipHomEquiv K A Y (internalHomFlipHomEquiv A K Y f) = f :=
    (internalHomFlipHomEquiv A K Y).symm_apply_apply f
  have he := internalHomFlipHomEquiv_app_zero (internalHomFlipHomEquiv A K Y f) a
  rw [hi] at he
  apply (functorVertexEquiv K Y).injective
  change functorVertex _ = _
  rw [Equiv.apply_symm_apply]
  exact he.symm

/-- 全 cofiber 四角形の族を、同じ全パラメーターを持つ関手圏の四角形へ移す。 -/
def cofiberFamilySquare {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (p : A ⟶ cofiberDiagrams B.obj) :
    Δ[1] ⊗ Δ[1] ⟶ (ihom A).obj B.obj :=
  internalHomFlipHomEquiv A (Δ[1] ⊗ Δ[1]) B.obj
    (p ≫ (fullSubcomplexOnVertices _ IsCofiberDiagramVertex).ι)

/-- 転置した族を各点で評価すると、元の同じ実四角形を回収する。 -/
lemma cofiberFamilySquare_evaluate {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (p : A ⟶ cofiberDiagrams B.obj) (a : A _⦋0⦌) :
    cofiberFamilySquare p ≫ evaluateFunctorAt a =
      squareDiagram (p.app (Opposite.op ⦋0⦌) a).val :=
  flipFamily_evaluate _ a

/-- 転置した族の底辺は、元の底辺の族の転置そのもの。 -/
lemma cofiberFamilySquare_bottom {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (p : A ⟶ cofiberDiagrams B.obj) :
    squareBottomEdge ≫ cofiberFamilySquare p =
      internalHomFlipHomEquiv A Δ[1] B.obj (p ≫ cofiberProjection B.obj) := by
  unfold cofiberFamilySquare
  rw [← internalHomFlipHomEquiv_pre_app]
  exact congrArg (internalHomFlipHomEquiv A Δ[1] B.obj) (Category.assoc _ _ _)

/-- 族の零角は、関手圏でも実際に零対象である。 -/
lemma cofiberFamilySquare_zero {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (p : A ⟶ cofiberDiagrams B.obj) :
    IsZeroVertex (squareVertex (cofiberFamilySquare p) 0 1) := by
  change IsZeroVertex ((cofiberFamilySquare p).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1))
  rw [cofiberFamilySquare, internalHomFlipHomEquiv_app_zero]
  apply isZeroVertex_functorVertex_of_pointwise
  intro a
  have hz := (fullSubcomplexOnVertices_vertex (p.app (Opposite.op ⦋0⦌) a)).1
  have he := cofiberVertex_corner B (p.app (Opposite.op ⦋0⦌) a)
    (stdSimplex.obj₀Equiv.symm 0, stdSimplex.obj₀Equiv.symm 1)
  exact (congrArg IsZeroVertex he).mpr hz

/-- パラメーター付き cofiber を関手圏の零角を持つ三角形として保持する。 -/
def cofiberFamilyZeroTriangle {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (p : A ⟶ cofiberDiagrams B.obj) : ZeroTriangle ((ihom A).obj B.obj) :=
  ⟨cofiberFamilySquare p, cofiberFamilySquare_zero p⟩

/-- 転置した族は点ごとの普遍性から関手圏の実 cofiber 列である。 -/
lemma cofiberFamily_isCofiber {A : SSet.{u}} {B : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}}
    (p : A ⟶ cofiberDiagrams B.obj) : IsCofiberSequence (cofiberFamilyZeroTriangle p) := by
  apply (functor_zeroTriangle_pushout_iff (cofiberFamilyZeroTriangle p)).2
  intro a
  change IsPushoutSquare (cofiberFamilySquare p ≫ evaluateFunctorAt a)
  rw [cofiberFamilySquare_evaluate]
  exact (fullSubcomplexOnVertices_vertex (p.app (Opposite.op ⦋0⦌) a)).2

end SerrePositivity.KST.Fibration
