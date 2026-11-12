module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.PostcompositionHomotopy
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ArbitraryParameterAdjunct

/-!
概要：任意の添字 K について、元の同じ標準単位から後合成の ∞ 随伴を構成する。
方針：同じ標準単位の式と、直積パラメータ上の Hom 全単射を照合する。
規約：添字の quasicategory 性を仮定しない。使われ方：一般 coherent 極限の保存。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section

/-- 同じ標準単位の Hom 比較は、元の二胞体の uncurry と可換。 -/
lemma parameterUnitHomMap_uncurry {K A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (H : SSet.Homotopy (𝟙 X) (F ≫ G))
    (U : A ⟶ (ihom K).obj X) (V : A ⟶ (ihom K).obj Y)
    (α : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (U ≫ (ihom K).map F) V) :
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry (K := K) (A := A) (X := X)
      (U := U) (V := V ≫ (ihom K).map G) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionUnitHomotopy H K))) U V α) =
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) (uncurry U) (uncurry V)
      (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry (K := K) (A := A) (X := Y)
        (U := U ≫ (ihom K).map F) (V := V) α) := by
  have hm := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry_comp (K := K) (A := A) (X := X)
    (U := U) (V := U ≫ (ihom K).map F ≫ (ihom K).map G)
    (W := V ≫ (ihom K).map G)
    ((hoFunctor.map ((pre U).app ((ihom K).obj X))).toFunctor.map
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionUnitHomotopy H K))))
    ((hoFunctor.map ((ihom A).map ((ihom K).map G))).toFunctor.map α)
  exact hm.trans (congrArg₂ (· ≫ ·)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry_unit_precomp (K := K) (A := A) H U)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry_postcomp (K := K) (A := A) α G))

/-- 任意の関手パラメータ上の後合成の標準単位 Hom 比較は全単射。 -/
lemma parameterUnitHomMap_postcomposition_bijective {K A X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (𝟙 X) (F ≫ G))
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)))
    (U : A ⟶ (ihom K).obj X) (V : A ⟶ (ihom K).obj Y) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionUnitHomotopy H K))) U V) := by
  have hs := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry_bijective (K := K) (A := A) (X := Y) (U ≫ (ihom K).map F) V
  have ht := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry_bijective (K := K) (A := A) (X := X) U (V ≫ (ihom K).map G)
  have hb := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap_bijective
    (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)) hH
    (uncurry U) (uncurry V)
  constructor
  · intro α β he
    apply hs.injective
    apply hb.injective
    rw [← parameterUnitHomMap_uncurry, ← parameterUnitHomMap_uncurry, he]
  · intro β
    obtain ⟨αu, hαu⟩ := hb.surjective (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.functorHomUncurry (K := K) (A := A) (X := X)
      (U := U) (V := V ≫ (ihom K).map G) β)
    obtain ⟨α', rfl⟩ := hs.surjective αu
    refine ⟨α', ht.injective ?_⟩
    rw [parameterUnitHomMap_uncurry]
    exact hαu

/-- quasicategory パラメータ上の標準単位 Hom 比較も、同じ式で全単射。 -/
lemma qcatUnitHomMap_postcomposition_bijective {K A X Y : SSet.{u}}
    [Quasicategory A] [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (H : SSet.Homotopy (𝟙 X) (F ≫ G))
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)))
    (U : A ⟶ (ihom K).obj X) (V : A ⟶ (ihom K).obj Y) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionUnitHomotopy H K))) U V) := by
  have hb := parameterUnitHomMap_postcomposition_bijective H hH U V
  have he : _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap
      (SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionUnitHomotopy H K))) U V =
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatUnitHomMap (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionUnitHomotopy H K))) U V := by
    funext α
    exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.parameterUnitHomMap_eq _ U V α
  rw [← he]
  exact hb

/-- 任意の添字で、元の標準単位のホモトピーから後合成の ∞ 随伴を構成する。 -/
def postcompositionAdjunctionOfUnitHomotopy {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (𝟙 X) (F ≫ G))
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)))
    (K : SSet.{u}) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction ((ihom K).map F) ((ihom K).map G) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitHomBijective
    (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionUnitHomotopy H K)))
    (fun U V ↦ qcatUnitHomMap_postcomposition_bijective H hH U V)

/-- 構成した後合成の随伴の単位は、元の指定単位から作ったものと一致する。 -/
lemma postcompositionAdjunctionOfUnitHomotopy_unitHom {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {F : X ⟶ Y} {G : Y ⟶ X}
    (H : SSet.Homotopy (𝟙 X) (F ≫ G))
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition
      (SSet.Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)))
    (K : SSet.{u}) : (postcompositionAdjunctionOfUnitHomotopy H hH K).unitHom =
      SSet.Truncated.HomotopyCategory.homMk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.postcompositionUnitHomotopy H K)) := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.qcatAdjunctionOfUnitHomBijective_unitHom _
    (fun U V ↦ qcatUnitHomMap_postcomposition_bijective H hH U V)

/-- 元の ∞ 随伴を、任意の添字の関手圏の後合成の ∞ 随伴に移す。 -/
def postcompositionAdjunction {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {F : X ⟶ Y} {G : Y ⟶ X} (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction F G) (K : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction ((ihom K).map F) ((ihom K).map G) := by
  have hH : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitMappingSpaceCondition (SSet.Truncated.HomotopyCategory.homMk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom))) := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy_hom]
    exact a.unitMappingSpaceCondition
  exact postcompositionAdjunctionOfUnitHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomHomotopy a.unitHom) hH K

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
