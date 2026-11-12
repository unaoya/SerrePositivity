module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceFiberPostcomposition
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceModelEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalFunctorMap

/-!
概要：coslice fiber と区間模型の比較の後合成に関する自然性。
方針：両端固定の join の族を後合成し、区間族に展開して比較する。
規約：α2b の intervalFunctorMap を共通の区間模型の作用として再利用する。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、coslice の比較を右 pinched 写像空間へ戻すための模型変更。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

attribute [local instance] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex_of_leftFibration

/-- 概要：標準の点の表示に揃えた coslice fiber の後合成。
方針：恒等族を join 上に展開して後合成し、像の両端で curry する。
規約：固定点の図式は Yoneda の逆写像で表示する。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、区間模型との厳密な自然性。 -/
def pointCosliceFiberMap {E F : SSet.{u}} (f : E ⟶ F) (x y : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm
        (f.app (Opposite.op ⦋0⦌) x))) (f.app (Opposite.op ⦋0⦌) y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberCurry (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry (𝟙 _) ≫ f)
    (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry_inl, SSet.yonedaEquiv_symm_comp])
    (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry_inr, SSet.const_comp])

/-- 概要：標準表示の後合成は任意の join 族を後合成して展開する操作と一致する。
方針：curry・uncurry の往復とパラメータの自然性を使う。
規約：パラメータの単体集合 A は任意。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、比較射の自然性の計算。 -/
lemma pointCosliceFiberMap_uncurry {A E F : SSet.{u}} {x y : E _⦋0⦌}
    (a : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) (f : E ⟶ F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry (a ≫ pointCosliceFiberMap f x y) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry a ≫ f := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry_precomp]
  unfold pointCosliceFiberMap
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry_curry, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberUncurry_precomp,
    Category.comp_id]

/-- 概要：coslice fiber の区間模型への比較射は後合成に自然。
方針：両辺を区間族へ展開し、join 族の後合成の計算を使う。
規約：区間模型の作用には α2b の intervalFunctorMap を使う。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、充満忠実性の模型によらない比較。 -/
lemma cosliceIntervalComparison_naturality {E F : SSet.{u}} (f : E ⟶ F) (x y : E _⦋0⦌) :
    pointCosliceFiberMap f x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace
        (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap f x y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace_uncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap_uncurry]
  have hp := pointCosliceFiberMap_uncurry
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y)) f
  simp only [Category.id_comp] at hp
  rw [hp]
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace_uncurry
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (SSet.yonedaEquiv.symm x)) y))
  simpa only [Category.id_comp, Category.assoc] using
    congrArg (fun a ↦ a ≫ f) h.symm

/-- 概要：α2b の右 pinched 比較は F1 の既存の比較射と一致する。
方針：両辺を区間族へ展開し、同じ join 族の表示を確認する。
規約：比較射の逆の選択には依存しない。
使われ方：Kerodon §4.6.5（Tag 01KW）–4.6.6（Tag 04HY）、右 pinched の自然性の再利用。 -/
lemma pinchedInterval_comparison_eq {E : SSet.{u}} (x y : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_uncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y))
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_uncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y))
  simpa only [Category.id_comp] using hl.trans hr.symm

/-- 概要：F1 の右 pinched 比較も α2b の区間模型の作用に自然。
方針：α2b の自然性定理の比較射を F1 の既存の比較に置き換える。
規約：単体集合の射の厳密な等式。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、右 pinched 写像空間の同値条件への復帰。 -/
lemma pinchedHomToIntervalMappingSpace_naturality {E F : SSet.{u}}
    (f : E ⟶ F) (x y : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap f x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace
        (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap f x y := by
  simpa only [pinchedInterval_comparison_eq] using _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.pinchedIntervalComparison_naturality f x y

/-- 概要：点の coslice fiber の後合成が同値である条件は右 pinched 写像空間の同値条件と一致する。
方針：両模型から共通の区間模型への自然な同値に同値の二つから三つ目を得る性質を使う。
規約：両全空間は quasicategory。
使われ方：Kerodon Proposition 5.1.6.7（Tag 01VB）、cocartesian 三角形の比較を充満忠実性へ移す。 -/
lemma pointCosliceFiberMap_equivalence_iff_pinchedHomMap
    {E F : SSet.{u}} [Quasicategory E] [Quasicategory F]
    (f : E ⟶ F) (x y : E _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (pointCosliceFiberMap f x y) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap f x y) := by
  have c0 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace_isQCatEquivalence x y
  have c1 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.cosliceFiberToIntervalMappingSpace_isQCatEquivalence
    (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)
  have r0 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y
  have r1 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence
    (f.app (Opposite.op ⦋0⦌) x) (f.app (Opposite.op ⦋0⦌) y)
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (pointCosliceFiberMap f x y) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap f x y) := by
    constructor
    · intro h
      apply c0.cancel_left
      rw [← cosliceIntervalComparison_naturality]
      exact h.comp c1
    · intro h
      apply c1.cancel_right
      rw [cosliceIntervalComparison_naturality]
      exact c0.comp h
  have hr : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap f x y) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFunctorMap f x y) := by
    constructor
    · intro h
      apply r0.cancel_left
      rw [← pinchedHomToIntervalMappingSpace_naturality]
      exact h.comp r1
    · intro h
      apply r1.cancel_right
      rw [pinchedHomToIntervalMappingSpace_naturality]
      exact r0.comp h
  exact ⟨fun h ↦ (hr.mpr (hc.mp h)).isSimplicialHomotopyEquivalence,
    fun h ↦ hc.mpr (hr.mp h.isQCatEquivalence)⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
