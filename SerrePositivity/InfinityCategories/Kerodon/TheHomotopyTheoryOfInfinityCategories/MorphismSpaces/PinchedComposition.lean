module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RightIntervalEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.IntervalComposition

/-!
概要：区間模型の射と対象作用を右 pinched 模型へ移す。
方針：模型比較とその選んだ逆で共役し、合成との整合を可逆二胞体で述べる。
規約：比較の逆は既存の comparison_isQCatEquivalence の同じ選択を使う。
使われ方：随伴の pinched 写像空間比較の対象自然性。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：区間模型の射を右 pinched 模型へ移す。
方針：始域の比較、指定射、終域の比較の逆を合成する。
規約：二つの周囲の quasicategory は異なってよい。
使われ方：対象変数の作用と adjunct 比較の共通の移送。 -/
noncomputable def liftMap {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom y₀ y₁ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x₀ x₁ ≫ f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence y₀ y₁).choose.inv

/-- 概要：模型の移送は射の合成を可逆二胞体まで保つ。
方針：中間の比較の逆と比較の合成を相殺する。
規約：厳密な等式ではなく h Fun の同型。
使われ方：自然性の正方形の pinched 模型への移送。 -/
noncomputable def liftMapCompIso {X Y Z : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] [Quasicategory Z]
    {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌} {z₀ z₁ : Z _⦋0⦌}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁)
    (g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace z₀ z₁) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (liftMap f ≫ liftMap g) (liftMap (f ≫ g)) := by
  simpa only [liftMap, Category.assoc, Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.choose] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence y₀ y₁).choose.invHomIso
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x₀ x₁ ≫ f))
      (g ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence z₀ z₁).choose.inv)

/-- 概要：模型の移送は可逆二胞体を保つ。
方針：比較による前合成とその逆による後合成を行う。
規約：同じ両端を持つ二つの区間模型の射。
使われ方：区間模型の自然性ホモトピーの移送。 -/
noncomputable def liftMapIso {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (liftMap f) (liftMap g) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.postcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x₀ x₁))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence y₀ y₁).choose.inv

/-- 概要：hX の射による右 pinched 写像空間への前合成。
方針：区間模型の前合成作用を比較で移す。
規約：始域変数に反変な作用。
使われ方：随伴比較の始域変数自然性。 -/
noncomputable def precompose {X : SSet.{u}} [Quasicategory X]
    {x' x : X _⦋0⦌} (y : X _⦋0⦌)
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x' y := liftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose y γ)

/-- 概要：hX の射による右 pinched 写像空間への後合成。
方針：区間模型の後合成作用を比較で移す。
規約：終域変数に共変な作用。
使われ方：随伴比較の終域変数自然性。 -/
noncomputable def postcompose {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) {y y' : X _⦋0⦌}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y' := liftMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose x δ)

/-- 概要：恒等射の移送は恒等射に同型。
方針：始域の模型比較と逆の合成を相殺する。
規約：h Fun の同型として述べる。
使われ方：pinched 模型の対象作用の恒等則。 -/
noncomputable def liftMapIdIso {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (liftMap (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x y))) (𝟙 _) := by
  simpa only [liftMap, Category.id_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.choose] using
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence x y).choose.homInvIso

/-- 概要：移した射は模型比較と可逆二胞体まで可換。
方針：終域の比較の逆と比較を相殺する。
規約：任意の二つの写像空間の間の射。
使われ方：pinched の前後合成が区間模型の標準作用を表すことの指定。 -/
noncomputable def liftMapComparisonIso {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y]
    {x₀ x₁ : X _⦋0⦌} {y₀ y₁ : Y _⦋0⦌}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x₀ x₁ ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y₁) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (liftMap f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace y₀ y₁) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x₀ x₁ ≫ f) := by
  simpa only [liftMap, Category.assoc, Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence.choose] using
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace_isQCatEquivalence y₀ y₁).choose.invHomIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomToIntervalMappingSpace x₀ x₁ ≫ f)

/-- 概要：pinched の前合成作用の恒等則。
方針：区間模型の恒等則を移す。
規約：h Fun の同型。
使われ方：対象変数の作用の単位。 -/
noncomputable def precomposeIdIso {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (precompose y (𝟙 (HomotopyCategory.mk x))) (𝟙 _) :=
  liftMapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_id x y).some) ≪≫
    liftMapIdIso x y

/-- 概要：pinched の後合成作用の恒等則。
方針：区間模型の恒等則を移す。
規約：h Fun の同型。
使われ方：対象変数の作用の単位。 -/
noncomputable def postcomposeIdIso {X : SSet.{u}} [Quasicategory X] (x y : X _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (postcompose x (𝟙 (HomotopyCategory.mk y))) (𝟙 _) :=
  liftMapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose_id x y).some) ≪≫
    liftMapIdIso x y

/-- 概要：pinched の前合成作用の合成則。
方針：移送の合成同型と区間模型の合成則を合わせる。
規約：始域変数に反変な順序。
使われ方：対象変数の作用の結合。 -/
noncomputable def precomposeCompIso {X : SSet.{u}} [Quasicategory X]
    {x'' x' x : X _⦋0⦌} (y : X _⦋0⦌)
    (γ' : (HomotopyCategory.mk x'' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x')
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (precompose y γ ≫ precompose y γ') (precompose y (γ' ≫ γ)) :=
  liftMapCompIso _ _ ≪≫
    liftMapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_comp y γ' γ).some)

/-- 概要：pinched の後合成作用の合成則。
方針：移送の合成同型と区間模型の合成則を合わせる。
規約：終域変数に共変な順序。
使われ方：対象変数の作用の結合。 -/
noncomputable def postcomposeCompIso {X : SSet.{u}} [Quasicategory X]
    (x : X _⦋0⦌) {y y' y'' : X _⦋0⦌}
    (δ : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk y')
    (δ' : (HomotopyCategory.mk y' : hoFunctor.obj X) ⟶ HomotopyCategory.mk y'') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (postcompose x δ ≫ postcompose x δ') (postcompose x (δ ≫ δ')) :=
  liftMapCompIso _ _ ≪≫
    liftMapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPostcompose_comp x δ δ').some)

/-- 概要：pinched の前後合成作用は可逆二胞体まで可換。
方針：区間模型の可換ホモトピーを移す。
規約：二つの対象変数の射は任意の hX の射。
使われ方：二変数の対象作用の整合。 -/
noncomputable def precomposePostcomposeIso {X : SSet.{u}} [Quasicategory X]
    {x' x y y' : X _⦋0⦌}
    (γ : (HomotopyCategory.mk x' : hoFunctor.obj X) ⟶ HomotopyCategory.mk x)
    (δ : (HomotopyCategory.mk y : hoFunctor.obj X) ⟶ HomotopyCategory.mk y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (precompose y γ ≫ postcompose x' δ)
      (postcompose x δ ≫ precompose y' γ) :=
  liftMapCompIso _ _ ≪≫
    liftMapIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalPrecompose_postcompose γ δ).some) ≪≫
    (liftMapCompIso _ _).symm

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
