module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerveNatTrans
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource

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
namespace SerrePositivity.EInfinity.ComplexLimits
open SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded SSet
open SerrePositivity.SimplicialModel
open scoped Simplicial
variable (A : Type u) [CommRing A] {I : Type (u + 1)} [Category.{u} I]
  {F G : I ⥤ Complex A} (η : F ⟶ G)

def complexOrdinaryDerivedNatTransHomotopy :
    SSet.Homotopy (nerveMap F ≫ complexOrdinaryDerivedSource A)
      (nerveMap G ≫ complexOrdinaryDerivedSource A) :=
  HomotopyClasses.postHomotopy (complexOrdinaryDerivedSource A) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy η)

lemma complexOrdinaryDerivedNatTransHomotopy_component (i : I) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (complexOrdinaryDerivedNatTransHomotopy A η)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)).edge = ((nerve.edgeMk (η.app i)).map
        (complexOrdinaryDerivedSource A)).edge :=
  congrArg ((complexOrdinaryDerivedSource A).app (Opposite.op ⦋1⦌))
    (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.MixedNerve.homotopy_component η i)

def complexOrdinaryDerivedNatTransIso (hη : ∀ i, QuasiIso (η.app i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap F ≫ complexOrdinaryDerivedSource A)
      (nerveMap G ≫ complexOrdinaryDerivedSource A) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.functorIsoOfPointwiseInvertibleHomotopy (complexOrdinaryDerivedNatTransHomotopy A η)
  intro z
  obtain ⟨i, rfl⟩ := ComposableArrows.mk₀_surjective z
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr
    (e := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (complexOrdinaryDerivedNatTransHomotopy A η)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex i)).toTruncated)
    (f := ((nerve.edgeMk (η.app i)).map (complexOrdinaryDerivedSource A)).toTruncated)
    (complexOrdinaryDerivedNatTransHomotopy_component A η i)).mpr
      (complexOrdinaryDerivedSource_map_weak A (η.app i) (hη i))

end SerrePositivity.EInfinity.ComplexLimits
