module
public import SerrePositivity.KST.SConstruction.CofiberObjectKClass
public import SerrePositivity.KST.SConstruction.ObjectKClassInvariance
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PretriangulatedInstance
public import SerrePositivity.CategoryTheory.TriangulatedK0

/-! # 三角圏の K₀ から実際の BF 零次 K 群への写像
概要：元の対象 K 類を、ホモトピー圏の三角圏 Grothendieck 群へ降ろす。
方針：全 cofiber 図式の加法関係を distinguished triangle の同型閉包へ移す。
規約：全単射性は別途証明が必要。使われ方：π₀ K と三角圏 K₀ の比較の順方向。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Pretriangulated SSet
open SerrePositivity.InfinityCategories
open Spectra
open scoped Simplicial

/-- 元の零角つき cofiber 列を同じ正方形の cofiber 図式の頂点へ移す。 -/
def cofiberDiagramOfZeroTriangle {C : SSet.{u}} (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle C)
    (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) : (cofiberDiagrams C) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square, by
    intro α
    have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
    rw [hα, op_id, CategoryTheory.Functor.map_id_apply]
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square)) 0 1) ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square))
    have hv : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square) = t.square :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).symm_apply_apply t.square
    rw [hv]
    exact ⟨t.zero_corner, ht⟩⟩

/-- 元の cofiber 列の三角形の対象 K 類は三角形の加法関係を満たす。 -/
lemma homotopyObjectKClass_cofiberTriangle (X : StableModel.{u})
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X.carrier) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    homotopyObjectKClass X (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht).obj₂ =
      homotopyObjectKClass X (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht).obj₁ +
        homotopyObjectKClass X (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberTriangle t ht).obj₃ := by
  have h := objectKClass_cofiber X (cofiberDiagramOfZeroTriangle t ht)
  change objectKClass X (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square)) 1 0) =
    objectKClass X (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square)) 0 0) +
      objectKClass X (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square)) 1 1) at h
  have hv : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex t.square) = t.square :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ X.carrier).symm_apply_apply t.square
  rw [hv] at h
  exact h

/-- ホモトピー圏の任意の distinguished triangle で実際の対象 K 類は加法的。 -/
lemma homotopyObjectKClass_triangle (X : StableModel.{u})
    (T : Triangle (hoFunctor.obj X.carrier)) (hT : T ∈ distTriang (hoFunctor.obj X.carrier)) :
    homotopyObjectKClass X T.obj₂ =
      homotopyObjectKClass X T.obj₁ + homotopyObjectKClass X T.obj₃ := by
  change T ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.cofiberDistinguishedTriangles X.carrier at hT
  obtain ⟨t, ht, ⟨e⟩⟩ := hT
  have h₁ := homotopyObjectKClass_iso X (Triangle.π₁.mapIso e)
  have h₂ := homotopyObjectKClass_iso X (Triangle.π₂.mapIso e)
  have h₃ := homotopyObjectKClass_iso X (Triangle.π₃.mapIso e)
  exact h₂.trans ((homotopyObjectKClass_cofiberTriangle X t ht).trans
    (congrArg₂ (· + ·) h₁.symm h₃.symm))

/-- ホモトピー圏の三角圏 K₀ から実際の BF 零次 K 群への対象類を保つ準同型。 -/
def triangulatedKZeroMap (X : StableModel.{u}) :
    TriangulatedK0 (hoFunctor.obj X.carrier) →+
      Additive (OmegaSpectrum.homotopyGroup (kOmegaSpectrum X) 0) :=
  TriangulatedK0.lift (homotopyObjectKClass X) (homotopyObjectKClass_iso X)
    (homotopyObjectKClass_triangle X)

/-- 比較準同型はホモトピー圏の各対象の類を元の BF K 類へ送る。 -/
lemma triangulatedKZeroMap_mk (X : StableModel.{u}) (a : hoFunctor.obj X.carrier) :
    triangulatedKZeroMap X (TriangulatedK0.mk a) = homotopyObjectKClass X a :=
  TriangulatedK0.lift_mk _ _ _ a

/-- 元の頂点の三角圏 K₀ 類の像は元の対象 K 類そのもの。 -/
lemma triangulatedKZeroMap_vertex (X : StableModel.{u}) (x : X.carrier _⦋0⦌) :
    triangulatedKZeroMap X (TriangulatedK0.mk (SSet.HomotopyCategory.mk x)) =
      objectKClass X x := triangulatedKZeroMap_mk X _

end SerrePositivity.KST.SConstruction
