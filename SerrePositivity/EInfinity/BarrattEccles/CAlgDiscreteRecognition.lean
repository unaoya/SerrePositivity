module

public import SerrePositivity.EInfinity.BarrattEccles.CAlgUnderlyingHomology
public import SerrePositivity.EInfinity.BarrattEccles.CAlgZeroDegreeDiscrete
public import SerrePositivity.EInfinity.BarrattEccles.CAlgVertexPresentation

/-!
# 同じ U による CAlg_R の離散対象の特徴付け

概要：U 像の全非零次数のホモロジー消滅は元の離散入力の本質像と同値。
方針：任意頂点の元の代数表示から実擬同型 span を通し、逆は同じホモロジー比較を使う。
規約：元の CAlg_R・U・離散入力を保持する。
使われ方：E2b の離散対象と G1′ の離散性条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories DifferentialGraded
open scoped Simplicial
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma cAlgUnderlyingDisc_of_iso {x y : (CAlg_R A) _⦋0⦌} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x y)
    (h : cAlgUnderlyingDisc A x) : cAlgUnderlyingDisc A y := by
  let e' := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.pathToEdgeHomotopyCategory
    ((truncation 2).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory A))).mapIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map e (cAlgForgetDerived A))
  intro i hi
  exact (h i hi).of_iso ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyFunctor A i).mapIso e').symm

lemma discreteCAlgEmbedding_underlyingDisc (B : CommAlgCat.{u} A) :
    cAlgUnderlyingDisc A
      ((discreteCAlgEmbedding A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B)) := by
  have : ((discreteAlgebraFunctor A).obj B).carrier.IsLE 0 := by
    change (cochainSingleZero (ModuleCat.of A B)).IsLE 0
    infer_instance
  have : ((discreteAlgebraFunctor A).obj B).carrier.IsGE 0 := by
    change (cochainSingleZero (ModuleCat.of A B)).IsGE 0
    infer_instance
  exact cAlgUnderlyingDisc_of_iso A (discreteCAlgEmbedding_vertexIso A B).symm
    (cAlgVertex_underlyingDisc A ((discreteAlgebraFunctor A).obj B))

def cAlgUnderlyingDiscDiscreteIso (x : (CAlg_R A) _⦋0⦌) (h : cAlgUnderlyingDisc A x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x ((discreteCAlgEmbedding A).app (Opposite.op ⦋0⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (zeroDegreeDiscreteAlgebra A (cAlgVertexRepresentative A x)))) := by
  have hx := cAlgUnderlyingDisc_of_iso A (cAlgVertexRepresentativeIso A x).symm h
  have := cAlgVertex_underlyingDisc_isLE A (cAlgVertexRepresentative A x) hx
  have := cAlgVertex_underlyingDisc_isGE A (cAlgVertexRepresentative A x) hx
  exact (cAlgVertexRepresentativeIso A x).symm ≪≫
    cAlgZeroDegreeDiscreteIso A (cAlgVertexRepresentative A x)

theorem cAlgUnderlyingDisc_iff_discrete (x : (CAlg_R A) _⦋0⦌) :
    cAlgUnderlyingDisc A x ↔ ∃ B : CommAlgCat.{u} A,
      Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x ((discreteCAlgEmbedding A).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex B))) := by
  constructor
  · intro h
    exact ⟨_, ⟨cAlgUnderlyingDiscDiscreteIso A x h⟩⟩
  · rintro ⟨B, ⟨e⟩⟩
    exact cAlgUnderlyingDisc_of_iso A e.symm (discreteCAlgEmbedding_underlyingDisc A B)

end SerrePositivity.EInfinity.BarrattEccles
