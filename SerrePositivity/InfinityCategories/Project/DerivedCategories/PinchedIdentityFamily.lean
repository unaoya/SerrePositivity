module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.ConstantEdgeFamily
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.PinchedEndpointTransport
/-!
概要：実恒等辺を表す pinched 頂点の定数族と、任意関手・端点輸送との両立を記録する。
方針：辺との頂点同値、退化写像の自然性、定値関手の恒等保存を使う。
規約：恒等辺の同じ実一次単体を保つ。使われ方：全降下選択空間上の単位整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory SSet
open scoped _root_.Simplicial
/-- 実恒等辺そのものを表す pinched Hom の頂点。 -/
def pinchedIdentityVertex {X : SSet.{u}} (x : X _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x x) _⦋0⦌ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x x).symm (Truncated.Edge.id (X := (truncation 2).obj X) x)
/-- 任意関手は、実恒等 pinched 頂点を実恒等 pinched 頂点に厳密に送る。 -/
lemma pinchedHomMap_identityVertex {X Y : SSet.{u}} (F : X ⟶ Y) (x : X _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap F x x).app (Opposite.op ⦋0⦌) (pinchedIdentityVertex x) =
      pinchedIdentityVertex (F.app (Opposite.op ⦋0⦌) x) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  exact ConcreteCategory.congr_hom (F.naturality (SimplexCategory.σ (0 : Fin 1)).op) x
/-- 頂点の等式輸送は実恒等 pinched 頂点を保つ。 -/
lemma pinchedIdentityVertex_transport {X : SSet.{u}} {x y : X _⦋0⦌} (h : x = y) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Roof.pinchedEndpointIso h h).hom.app (Opposite.op ⦋0⦌) (pinchedIdentityVertex x) =
      pinchedIdentityVertex y := by
  subst y
  rfl
/-- 実恒等頂点の定数族は、任意パラメータ関手圏の恒等射を表す。 -/
lemma pinchedFamilyHom_identity {K X : SSet.{u}} (x : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamilyHom (SSet.const (X := K) (pinchedIdentityVertex x) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x x) = 𝟙 _ := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.pinchedFamilyHom_const_vertex]
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x x (pinchedIdentityVertex x) =
      Truncated.Edge.id (X := (truncation 2).obj X) x :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomVertexEquiv x x).apply_symm_apply
      (Truncated.Edge.id (X := (truncation 2).obj X) x)
  rw [h, Truncated.HomotopyCategory.homMk_id]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.constantFunctorHomMap_id K x
end SerrePositivity.InfinityCategories.Project.DerivedCategories
