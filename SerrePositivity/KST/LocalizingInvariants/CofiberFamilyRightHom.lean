module
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamilyRightHom

public import SerrePositivity.KST.LocalizingInvariants.ArrowFamilyHomotopy
public import SerrePositivity.InfinityCategories.Stable.Exact.CofiberSquareFamily
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomWhiskering
public import SerrePositivity.InfinityCategories.Stable.CofiberFunctorMapping
public import SerrePositivity.InfinityCategories.Stable.CofiberZeroSource
public import SerrePositivity.InfinityCategories.Core.FunctorEdgePointwise

/-!
概要：元の cofiber 全族の右辺を自然変換として保持する。
方針：右辺の prism を取り出し、零始点の場合の可逆性を各成分から示す。
規約：cofiber の比較を選び直さない。使われ方：C 随伴単位との同時比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.CofiberFamily
variable (X : SSet.{u}) [Quasicategory X] [IsStable X]
  {A : SSet.{u}} (a : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)

lemma rightHomotopy_vertex_edge (x : A _⦋0⦌) :
    (simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHomotopy X a) x).edge =
      (squareRightArrow (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x)).edge := by
  change (simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.arrowFamilyHomotopy (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightArrow X a)) x).edge = _
  rw [arrowFamilyHomotopy_vertex_edge, squareRightArrow_edge]
  have hs : functorVertex (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x) = (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a).app _ x :=
    (functorVertexEquiv _ _).apply_symm_apply _
  change intervalFunctorVertexEdge (((pre squareRightEdge).app X).app _
    ((_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squares X a).app _ x)) = _
  rw [← hs]
  rfl

lemma rightHom_post_isIso_of_zeroSource {Y : SSet.{u}} [Quasicategory Y] [IsStable Y]
    (F : X ⟶ Y) [IsExactFunctor F]
    (hz : ∀ x : A _⦋0⦌, IsZeroVertex (F.app (Opposite.op ⦋0⦌)
      (squareVertex (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x) 0 0))) : IsIso (homPost F (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHom X a)) := by
  let H := functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHomotopy X a) F
  have hi : IsInvertibleEdge (functorEdgeOfSimplicialHomotopy H) := by
    apply functorEdgeOfSimplicialHomotopy_isInvertible_of_pointwise
    intro x
    have he : (simplicialHomotopyVertexEdge H x).edge =
        (squareRightArrow (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt X a x ≫ F)).edge := by
      change F.app (Opposite.op ⦋1⦌)
        (simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.rightHomotopy X a) x).edge = _
      rw [rightHomotopy_vertex_edge]
      rfl
    apply (isInvertibleEdge_congr
      (f := (simplicialHomotopyVertexEdge H x).toTruncated) he.symm).mp
    exact isIso_squareHoRight_of_pushout_initial_left _
      (IsExactFunctor.preservesPushoutSquare F _ (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt_isPushout X a x))
      (hz x).1 (IsExactFunctor.preservesZero (F := F) _ (_root_.SerrePositivity.InfinityCategories.Stable.Exact.CofiberFamily.squareAt_zero X a x)).1
  change IsIso (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy H)) at hi
  rw [functorHomotopyPostcomp_hom] at hi
  exact hi

end SerrePositivity.KST.LocalizingInvariants.CofiberFamily
