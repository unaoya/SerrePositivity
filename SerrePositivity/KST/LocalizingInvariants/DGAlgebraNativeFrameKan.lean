module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNativeMixedFrame
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellMappingLargeKan
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakEquivalence

/-!
概要：実始域 frame の Hom と混合比較の共通置換を、大宇宙の Kan 値関手に束ねる。
方針：実 frame の Kan 条件と既存の関手的 Kan 置換を適用し、元の全標的射を使う。
規約：モデル構造・Kan 条件・置換の存在を新しい入力にしない。
使われ方：実 AW 写像図式と実始域 frame 図式の全自然な空間値比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded SerrePositivity.Reedy
open SerrePositivity.InfinityCategories SerrePositivity.HomotopyFunctionComplex

namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] (A : Mon (Complex R))

attribute [local instance] EInfinity.DGAlgebra.modelCategory
  EInfinity.DGAlgebra.hasFiniteLimits EInfinity.DGAlgebra.hasTerminal

lemma nativeCellSourceFrameHom_kanComplex (B : Mon (Complex R)) :
    SSet.KanComplex ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (nativeCellSourceFrame R A)).obj B) := by
  have : IsFibrant B := EInfinity.DGAlgebra.allFibrant R B
  exact cosimplicialHom_kanComplex (nativeCellSourceFrame R A)
    ((nativeModelSourceResolutionFamily R).cofibrant (cellResolution R A))
    ((nativeModelSourceResolutionFamily R).atObject (cellResolution R A)).homotopicallyConstant B

def nativeCellSourceFrameLargeKanFunctor : Mon (Complex R) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1} where
  obj B := ⟨SSet.uliftFunctor.{u + 1, u}.obj
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (nativeCellSourceFrame R A)).obj B), by
      have := nativeCellSourceFrameHom_kanComplex R A B
      infer_instance⟩
  map f := SSet.uliftFunctor.{u + 1, u}.map
    ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (nativeCellSourceFrame R A)).map f)
  map_id B := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (nativeCellSourceFrame R A) ⋙
    SSet.uliftFunctor.{u + 1, u}).map_id B
  map_comp f g := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (nativeCellSourceFrame R A) ⋙
    SSet.uliftFunctor.{u + 1, u}).map_comp f g

def nativeCellMixedReplacementLargeKanFunctor : Mon (Complex R) ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1} where
  obj B := ⟨SSet.uliftFunctor.{u + 1, u}.obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.obj ((nativeCellMixedMappingFunctor R A).obj B)), inferInstance⟩
  map f := SSet.uliftFunctor.{u + 1, u}.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map ((nativeCellMixedMappingFunctor R A).map f))
  map_id B := (nativeCellMixedMappingFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement ⋙
    SSet.uliftFunctor.{u + 1, u}).map_id B
  map_comp f g := (nativeCellMixedMappingFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement ⋙
    SSet.uliftFunctor.{u + 1, u}).map_comp f g

lemma nativeCellSourceFrameLargeKanFunctor_forget :
    nativeCellSourceFrameLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom (nativeCellSourceFrame R A) ⋙ SSet.uliftFunctor.{u + 1, u} := rfl

lemma nativeCellMixedReplacementLargeKanFunctor_forget :
    nativeCellMixedReplacementLargeKanFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget =
      nativeCellMixedMappingFunctor R A ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement ⋙
        SSet.uliftFunctor.{u + 1, u} := rfl

def nativeCellSourceFrameInfinityKanFunctor : InfinityPresentation R ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1} :=
  ULiftHom.down ⋙ nativeCellSourceFrameLargeKanFunctor R A

def nativeCellMixedReplacementInfinityKanFunctor : InfinityPresentation R ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u + 1} :=
  ULiftHom.down ⋙ nativeCellMixedReplacementLargeKanFunctor R A

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
