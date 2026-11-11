module
public import SerrePositivity.KST.Fibration.WeakStringCofibers

/-! # 全合成辺の元の cofiber 四角形の回収

完全関手として構成した補完の各頂点を実四角形として読み、
底辺が元の合成辺であることと cofiber が商で零になることを照合する。
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

/-- 完全な補完の各頂点が持つ、元の全 cofiber 四角形。 -/
def weakStringCofiberVertex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) (v : (weakStringCategory q n) _⦋0⦌) :
    (cofiberDiagrams B.obj) _⦋0⦌ :=
  ((weakStringCofiberExact q α).val.app (Opposite.op ⦋0⦌) v).val

/-- 各実四角形の底辺の一次単体は、元の列の指定した合成辺そのもの。 -/
lemma weakStringCofiberVertex_bottom {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) (v : (weakStringCategory q n) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (weakStringCofiberVertex q α v).val)).edge =
      B.obj.map α.op (simplexVertexValue n v.val) := by
  have hp := congrArg Subtype.val (ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg Subtype.val (weakStringCofiberExact_projection q α))
      (Opposite.op ⦋0⦌)) v)
  change (cofiberProjection B.obj).app (Opposite.op ⦋0⦌) (weakStringCofiberVertex q α v) =
    ((pre (stdSimplex.map α)).app B.obj).app (Opposite.op ⦋0⦌) v.val at hp
  rw [← cofiberProjection_vertex_simplex, hp]
  exact simplexVertexValue_reindex α v.val

/-- 同じ実四角形の cofiber は商で零である。 -/
lemma weakCofiberVertex_kernel {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    (w : (cofiberDiagrams B.obj) _⦋0⦌)
    (hw : (relativeCofiberPredicate (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).predicate w) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌) (vertexCofiberSquare w).cofiber) := by
  have hk := hw.2
  have he : (cofiberStableQuotient (sInputModel B)).val.app (Opposite.op ⦋0⦌) w =
      (vertexCofiberSquare w).cofiber :=
    cofiberVertex_corner B w (stdSimplex.obj₀Equiv.symm 1, stdSimplex.obj₀Equiv.symm 1)
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌)
    ((cofiberStableQuotient (sInputModel B)).val.app (Opposite.op ⦋0⦌) w)) at hk
  rw [he] at hk
  exact hk

/-- 選択した全合成辺の同じ実四角形の cofiber は商で零である。 -/
lemma weakStringCofiberVertex_kernel {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) (v : (weakStringCategory q n) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (q.hom.app (Opposite.op ⦋0⦌)
      (vertexCofiberSquare (B := B) (weakStringCofiberVertex q α v)).cofiber) := by
  have hw : (relativeCofiberPredicate (ClosedStablePredicate.top (sInputModel B))
      (kernelClosedPredicate q)).predicate (weakStringCofiberVertex q α v) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex
      ((weakStringCofiberExact q α).val.app (Opposite.op ⦋0⦌) v)
  exact weakCofiberVertex_kernel q (weakStringCofiberVertex q α v) hw

/-- 再添字は同値な別の四角形に移さず、元の実四角形を厳密に保つ。 -/
lemma weakStringCofiberVertex_reindex {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {m n : SimplexCategory} (θ : m ⟶ n) (α : ⦋1⦌ ⟶ m)
    (v : (weakStringCategory q n) _⦋0⦌) :
    weakStringCofiberVertex q α ((weakStringMap q θ).app (Opposite.op ⦋0⦌) v) =
      weakStringCofiberVertex q (α ≫ θ) v :=
  congrArg (fun f : weakStringModel q n ⟶ weakCofiberModel q =>
    (f.val.app (Opposite.op ⦋0⦌) v).val) (weakStringCofiberExact_reindex q θ α)

/-- 選んだ cofiber の零性は、商を取る前の元の合成辺の可逆性で正確に判定される。 -/
lemma weakStringCofiberVertex_zero_iff {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C)
    {n : SimplexCategory} (α : ⦋1⦌ ⟶ n) (v : (weakStringCategory q n) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (vertexCofiberSquare (B := B) (weakStringCofiberVertex q α v)).cofiber ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (B.obj.map α.op (simplexVertexValue n v.val))) :=
  (vertexCofiberSquare (B := B) (weakStringCofiberVertex q α v)).homMk_isIso_iff_zero.symm.trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (weakStringCofiberVertex_bottom q α v))

end SerrePositivity.KST.Fibration
