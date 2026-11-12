module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ControlledTriangleEncoderMap
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ContractiblePrescribedRetraction

/-!
概要：頂点ごとの native Hom 回収を、単射 encoder の厳密左逆で保持する。
方針：encoder の像上では厳密逆を指定し、それ以外では既存の読出しを指定する。
規約：単射 encoder の存在はこの葉の結論に含めず、未解決の構成入力として明示する。
使われ方：Ind-S (9) の厳密切断を単射 encoder の実構成に還元する。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 単射の像上の逆と、任意の頂点関係を同時に保つ厳密左逆。 -/
lemma contractibleKan_exists_retraction_preserving_relation {L T : SSet.{u}}
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan L) (encode : L ⟶ T) [Mono encode]
    (R : L _⦋0⦌ → T _⦋0⦌ → Prop)
    (hencode : ∀ l, R l (encode.app (Opposite.op ⦋0⦌) l))
    (hread : ∀ t, ∃ l, R l t) :
    ∃ read : T ⟶ L, encode ≫ read = 𝟙 L ∧
      ∀ t, R (read.app (Opposite.op ⦋0⦌) t) t := by
  classical
  let v (t : T _⦋0⦌) : L _⦋0⦌ :=
    if h : ∃ l, encode.app (Opposite.op ⦋0⦌) l = t then h.choose else (hread t).choose
  have hv (t : T _⦋0⦌) : R (v t) t := by
    dsimp only [v]
    split_ifs with h
    · exact Eq.mp (congrArg (R h.choose) h.choose_spec) (hencode h.choose)
    · exact (hread t).choose_spec
  have hi (l : L _⦋0⦌) : v (encode.app (Opposite.op ⦋0⦌) l) = l := by
    dsimp only [v]
    split_ifs with h
    · exact (injective_of_mono (encode.app (Opposite.op ⦋0⦌))) h.choose_spec
    · exact False.elim (h ⟨l, rfl⟩)
  obtain ⟨read, hr, hv'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.contractibleKan_exists_retraction_with_vertices hc encode v hi
  refine ⟨read, hr, ?_⟩
  intro t
  rw [hv']
  exact hv t

/-- 元の二胞体と全長 Hom の、各 k における全 native Hom 回収関係。 -/
def controlledTriangleNativeRelation (X Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : SSet.{u + 1})
    (c : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Z))
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (l : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K c) _⦋0⦌)
    (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilySpace K a) _⦋0⦌) : Prop :=
  ∀ k : K _⦋0⦌,
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomValue l).app (Opposite.op ⦋0⦌) k)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex ((SSet.uliftFunctor.{u + 1, u}).map
        ((SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.familyAtVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilyValue t) k)).map
          ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)))

/-- 正しい native Hom を持つ単射 encoder があれば、実読出しを厳密左逆にできる。
単射 encoder 自体の存在と正規化後の全対角式は別途構成する。 -/
lemma controlledTriangleSplit_of_mono_encoder
    (X Y Z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (K : SSet.{u + 1})
    (f : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom X Y))
    (g : K ⟶ (SSet.uliftFunctor.{u + 1, u}).obj (SimplicialCategory.sHom Y Z))
    (a : (Λ[2, 1] : SSet.{u + 1}) ⊗ K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (hf : (horn₂₁.ι₀₁ ▷ K) ≫ a =
      (Δ[1] ◁ f) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison X Y))
    (hg : (horn₂₁.ι₁₂ ▷ K) ≫ a =
      (Δ[1] ◁ g) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomIntervalComparison Y Z))
    (encode : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilySpace K a) [Mono encode]
    (hencode : ∀ l, controlledTriangleNativeRelation X Z K
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g) a l (encode.app (Opposite.op ⦋0⦌) l)) :
    ∃ read : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleFamilySpace K a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace X Z K
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g),
      encode ≫ read = 𝟙 _ ∧ ∀ t, controlledTriangleNativeRelation X Z K
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleCompositeFamily X Y Z K f g) a (read.app (Opposite.op ⦋0⦌) t) t := by
  obtain ⟨r₀, hr₀⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleReadoutMap_exists X Y Z K f g a hf hg
  exact contractibleKan_exists_retraction_preserving_relation
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.controlledTriangleLongHomSpace_isContractibleKan X Z K _) encode _ hencode
    (fun t => ⟨r₀.app (Opposite.op ⦋0⦌) t, hr₀ t⟩)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
