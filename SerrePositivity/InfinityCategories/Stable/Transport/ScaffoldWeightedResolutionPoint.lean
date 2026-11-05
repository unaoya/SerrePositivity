module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.ScaffoldTransportComparisonSpan
public import Mathlib.AlgebraicTopology.SimplexCategory.Defs
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.Opposite
public import Mathlib.CategoryTheory.Category.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.NatTrans
public import Mathlib.CategoryTheory.Opposites
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Combinatorics.Quiver.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import SerrePositivity.InfinityCategories.Core.NerveCone
public import SerrePositivity.InfinityCategories.Core.RightFibration
public import SerrePositivity.InfinityCategories.Core.VertexFiber
public import SerrePositivity.InfinityCategories.F1.Categories.CatInfinity
public import SerrePositivity.InfinityCategories.F1.Categories.KanDiagramCoherentNerve
public import SerrePositivity.InfinityCategories.F1.Categories.PointedSpaces
public import SerrePositivity.InfinityCategories.F1.Fibrations.LeftCoherentTransportReconstruction
public import SerrePositivity.InfinityCategories.F1.KanModels.KanOppositeCoefficients
public import SerrePositivity.InfinityCategories.F1.KanModels.KanPointHomNaturality
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransport
public import SerrePositivity.InfinityCategories.F1.Transport.LeftStrictTransportWeightedNerve
public import SerrePositivity.InfinityCategories.PinchedHom.Basic

/-!
分割で生成：docstring を書き直すこと
 # 元の scaffold の同じ weighted 点を既存の左解像比較へ厳密に戻す
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan
end SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan
namespace SerrePositivity.InfinityCategories.Stable.Transport
open SerrePositivity.KST.Fibration
/-- fiber 点の値を変えず、底の頂点の表示だけを等号で変える。 -/
def vertexFiberPointReindex {E B : SSet.{u}} (q : E ⟶ B)
    {b b' : B _⦋0⦌} (h : b = b') (v : (vertexFiber q b) _⦋0⦌) :
    (vertexFiber q b') _⦋0⦌ :=
  ⟨v.val, v.property.trans (congrArg (fun z => PinchedHom.constant z 0) h)⟩

/-- 値を保つ表示は、同じ等号による標準の fiber 移送と一致する。 -/
theorem vertexFiberPointReindex_eq_transport {E B : SSet.{u}} (q : E ⟶ B)
    {b b' : B _⦋0⦌} (h : b = b') (v : (vertexFiber q b) _⦋0⦌) :
    vertexFiberPointReindex q h v =
      (eqToHom (congrArg (vertexFiber q) h)).app (Opposite.op ⦋0⦌) v := by
  subst b'
  rfl

namespace ScaffoldTransportComparisonSpan
open SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan
variable {I : Type u} [Category.{u} I] {E : SSet.{u}}
  {p : E ⟶ nerve I} [LeftFibration p] (s : ScaffoldTransportComparisonSpan p)

/-- 分類値の表示変更を、元の表現と元の Kan 値を明記して固定する。 -/
theorem coefficientResolutionVertexEq (c : I) :
    (leftCoherentTransport p).app (Opposite.op ⦋0⦌) (ULift.up (nerveVertex c)) =
      spaceInfinityVertex (kanObjectOpFunctor.obj ((leftStrictTransportFunctor p).obj c)) := by
  simpa only [leftCoherentTransport, Functor.comp_obj] using
    kanDiagramCoherentNerve_vertex (leftStrictTransportFunctor p ⋙ kanObjectOpFunctor) c

theorem fiberPoint_ext {E B : SSet.{u}} (q : E ⟶ B) (b : B _⦋0⦌)
    (v w : (vertexFiber q b) _⦋0⦌)
    (h : (vertexFiberι q b).app (Opposite.op ⦋0⦌) v =
      (vertexFiberι q b).app (Opposite.op ⦋0⦌) w) : v = w :=
  Subtype.ext h

/-- strict transport の忘却図式は元の単体集合値図式と厳密に一致。 -/
theorem strictTransportForget_eq :
    leftStrictTransportFunctor p ⋙ kanObjectForget = leftStrictTransportDiagram p := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro a b f
  rfl

end ScaffoldTransportComparisonSpan
end SerrePositivity.InfinityCategories.Stable.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Stable.Transport.vertexFiberPointReindex (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.vertexFiberPointReindex := _root_.SerrePositivity.InfinityCategories.Stable.Transport.vertexFiberPointReindex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.vertexFiberPointReindex_eq_transport := _root_.SerrePositivity.InfinityCategories.Stable.Transport.vertexFiberPointReindex_eq_transport

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq := _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.fiberPoint_ext := _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.fiberPoint_ext

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.strictTransportForget_eq := _root_.SerrePositivity.InfinityCategories.Stable.Transport.ScaffoldTransportComparisonSpan.strictTransportForget_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.vertexFiberPointReindex._proof_1 := _root_.SerrePositivity.InfinityCategories.Stable.Transport.vertexFiberPointReindex._proof_1
