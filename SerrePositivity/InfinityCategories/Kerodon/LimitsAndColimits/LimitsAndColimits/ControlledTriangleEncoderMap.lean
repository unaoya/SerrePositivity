module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleReadoutMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SplitTriangleNormalization

/-!
概要：合成端固定の長 Hom 全族空間から、元の全ホーンを持つ二胞体全族空間への実射。
方針：各長 Hom 全族の実制御二胞体を全頂点に指定し、可縮 Kan な二胞体空間へ延長する。
規約：単射性・厳密切断・全対角の標準像条件はここでは主張しない。
使われ方：Ind-S (9) の構成の全族写像化。最終の split encoder とは区別する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 合成端固定空間の一点が表す元の長 Hom 全族。 -/
def controlledTriangleLongHomValue {X Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} {K : SSet.{u + 1}}
    {c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)}
    (l : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K c) _⦋0⦌) :
    K ⟶ (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))).obj
      ((SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm l.val

/-- 長 Hom 全族を読むと、元の合成端の全族を厳密に回収する。 -/
lemma controlledTriangleLongHomValue_comp {X Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}} {K : SSet.{u + 1}}
    {c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z)}
    (l : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K c) _⦋0⦌) :
    controlledTriangleLongHomValue l ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
      (Y := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
      (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath)) = c := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
  have hl := l.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero _)
  change ((ihom K).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
    (X := (SSet.uliftFunctor.{u + 1, u}).obj (nerve _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleNativePath.{u}))
    (Y := (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
    (ULift.up (ComposableArrows.mk₀ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath)))).app (Opposite.op ⦋0⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (controlledTriangleLongHomValue l)) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex c
  rw [show _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (controlledTriangleLongHomValue l) = l.val from
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).apply_symm_apply l.val]
  exact hl

/-- 元の全ホーンを持つ実二胞体族を同じ fiber の頂点として登録する。 -/
def controlledTriangleFamilyVertex (K : SSet.{u + 1})
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (F : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hF : ((horn 2 (1 : Fin 3)).ι ▷ K) ≫ F = a) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilySpace K a) _⦋0⦌ :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F, by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (((horn 2 (1 : Fin 3)).ι ▷ K) ≫ F) = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a
    rw [hF]⟩

lemma controlledTriangleFamilyVertex_value (K : SSet.{u + 1})
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (F : (Δ[2] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (hF) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilyValue (controlledTriangleFamilyVertex K a F hF) = F :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm_apply_apply F

/-- 各入力の全 native Hom を回収する実 encoder 射。単射性と厳密切断は含まない。 -/
lemma controlledTriangleEncoderMap_exists
    (X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : SSet.{u + 1})
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hf : (horn₂₁.ι₀₁ ▷ K) ≫ a =
      (Δ[1] ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y))
    (hg : (horn₂₁.ι₁₂ ▷ K) ≫ a =
      (Δ[1] ◁ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison Y Z)) :
    ∃ encode : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g) ⟶
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilySpace K a,
      ∀ (l : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K
          (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)) _⦋0⦌) (k : K _⦋0⦌),
        HEq ((controlledTriangleLongHomValue l).app (Opposite.op ⦋0⦌) k)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
            ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex
              (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilyValue (encode.app (Opposite.op ⦋0⦌) l)) k)).map
              ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
  have enc (l : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g)) _⦋0⦌) :
      ∃ t : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilySpace K a) _⦋0⦌,
        ∀ k : K _⦋0⦌,
          HEq ((controlledTriangleLongHomValue l).app (Opposite.op ⦋0⦌) k)
            (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
              ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilyValue t) k)).map
                ⟨ULift.up 0⟩ ⟨ULift.up 2⟩))) := by
    obtain ⟨F, hF, hn⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamily_exists_of_longHom X Y Z K f g a hf hg
      (controlledTriangleLongHomValue l) (controlledTriangleLongHomValue_comp l)
    refine ⟨controlledTriangleFamilyVertex K a F hF, ?_⟩
    intro k
    rw [controlledTriangleFamilyVertex_value]
    exact hn k
  choose v hv using enc
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.contractibleKan_exists_map_with_vertices
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilySpace_isContractibleKan K a) v
  refine ⟨e, ?_⟩
  intro l k
  rw [he]
  exact hv l k

/-- 読出し・再構成の実射で得た点を、同じ元の全ホーンの fiber 内で可逆比較する。
この比較だけから厳密切断や全対角の標準像条件は結論しない。 -/
lemma controlledTriangleFamilyMaps_vertexIso
    (X Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (encode : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilySpace K a)
    (read : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilySpace K a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K c)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilySpace K a) _⦋0⦌) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso t ((read ≫ encode).app (Opposite.op ⦋0⦌) t)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.splitTriangleNormalization_vertexIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilySpace_isContractibleKan K a) encode read t

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
