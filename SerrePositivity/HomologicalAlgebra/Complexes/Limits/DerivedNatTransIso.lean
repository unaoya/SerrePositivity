module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveNatTrans
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.OrdinaryDerivedSource

/-!
# 元の複体値自然変換の全 D(R) 値比較

概要：全成分が準同型である同じ通常自然変換を全関手同型へ移す。
方針：混合宇宙の元の円柱と同じ準同型辺の反転を使う。
規約：元の全図式・指定自然変換・全単体を保持する。
使われ方：全 E 代数の置換後の忘却から元の非置換忘却への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.ComplexLimits
open _root_.SerrePositivity.InfinityCategories
open _root_.CategoryTheory _root_.SerrePositivity.DifferentialGraded _root_.SSet
open _root_.SerrePositivity.SimplicialModel
open scoped _root_.Simplicial
variable (A : Type u) [CommRing A] {I : Type (u + 1)} [Category.{u} I]
  {F G : I ⥤ Complex A} (η : F ⟶ G)

def complexOrdinaryDerivedNatTransHomotopy :
    SSet.Homotopy (nerveMap F ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)
      (nerveMap G ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) :=
  HomotopyClasses.postHomotopy (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy η)

lemma complexOrdinaryDerivedNatTransHomotopy_component (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHomotopy A η)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)).edge = ((nerve.edgeMk (η.app i)).map
        (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)).edge :=
  congrArg ((_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌))
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy_component η i)

def complexOrdinaryDerivedNatTransIso (hη : ∀ i, QuasiIso (η.app i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap F ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)
      (nerveMap G ≫ _root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHomotopy A η)
  intro z
  obtain ⟨i, rfl⟩ := ComposableArrows.mk₀_surjective z
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHomotopy A η)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)).toTruncated)
    (f := ((nerve.edgeMk (η.app i)).map (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource A)).toTruncated)
    (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedNatTransHomotopy_component A η i)).mpr
      (_root_.SerrePositivity.ComplexLimits.complexOrdinaryDerivedSource_map_weak A (η.app i) (hη i))

end SerrePositivity.ComplexLimits
