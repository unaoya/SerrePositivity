module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaLocalCriterion
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.UnitCommaArrowFamilies
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FunctorEdgePointwise

/-!
概要：指定 comma 頂点での単位比較の導来 fiber の標的族と普遍ホモトピーを取り出す。
方針：path 置換の引き戻しの path 成分を、元の普遍可逆 path ホモトピーへ代入する。
規約：元の導来 fiber の path 成分を保持し、別のホモトピー代表を選ばない。
使われ方：導来 fiber から comma の写像空間へ戻る射の入力。

対応節は Kerodon 6.2（Tag 02EH）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
variable {F : X ⟶ Y} {G : Y ⟶ X}

/-- 概要：指定された comma 頂点の矢印で取る標準単位比較の導来 fiber。
方針：既存の区間比較の導来 fiber を頂点の標的と矢印で特殊化する。
規約：新しい fiber 模型ではなく既存の定義の略記。
使われ方：戻る比較射の始域を簡潔に表示する。 -/
noncomputable abbrev unitCommaComparisonFiber
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) : SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalComparisonFiber η x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrowVertex G x w)

/-- 概要：導来 fiber から単位比較の元の始域への射。
方針：頂点 fiber の包含の後に path 置換の第二射影を続ける。
規約：始域は F(x) から w の標的への写像空間。
使われ方：戻る比較射の標的族。 -/
noncomputable def unitComparisonFiberSource
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) :
    unitCommaComparisonFiber η x w ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrowVertex G x w) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementProjection (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))

/-- 概要：導来 fiber が保持する元の可逆 path の族。
方針：頂点 fiber の包含と path 置換の第一射影を続ける。
規約：この path 成分からホモトピーを回収する。
使われ方：戻る比較の coherence の普遍データ。 -/
noncomputable def unitComparisonFiberPath
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) :
    unitCommaComparisonFiber η x w ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace x (G.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathReplacementMap
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrowVertex G x w) ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))

/-- 概要：導来 fiber の path の始点は標的族の標準単位比較による像。
方針：path 置換の引き戻し条件を使う。
規約：厳密な射の等式。
使われ方：普遍ホモトピーの始点条件。 -/
lemma unitComparisonFiberPath_start
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) :
    unitComparisonFiberPath η x w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0 =
      unitComparisonFiberSource η x w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w) := by
  rw [unitComparisonFiberPath, Category.assoc, pullback.condition]
  exact (Category.assoc _ _ _).symm

/-- 概要：導来 fiber の path の終点は指定した comma 頂点の矢印。
方針：path 置換の終点写像の頂点 fiber 条件を使う。
規約：指定頂点への定値射として述べる。
使われ方：普遍ホモトピーの終点条件。 -/
lemma unitComparisonFiberPath_end
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) :
    unitComparisonFiberPath η x w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 1 =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrowVertex G x w) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ pullback.fst _ _) ≫ _ = _
  rw [Category.assoc]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp _ _

/-- 概要：導来 fiber の元の path 成分から回収した普遍ホモトピー。
方針：可逆 path の普遍ホモトピーを前合成し、両端の厳密な式で正規化する。
規約：h Fun の等式からホモトピーを選び直さない。
使われ方：comma の正方形の復元に渡す。 -/
noncomputable def unitComparisonFiberHomotopy
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (x : X _⦋0⦌) (w : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiber G x) _⦋0⦌) :
    SSet.Homotopy
      (unitComparisonFiberSource η x w ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberTargetVertex G x w))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrowFamily G x w (unitCommaComparisonFiber η x w)) where
  h := (unitComparisonFiberPath η x w ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathHomotopy _).h
  h₀ := by
    have h : SSet.ι₀ ≫ (unitComparisonFiberPath η x w ▷ (Δ[1] : SSet.{u})) =
        unitComparisonFiberPath η x w ≫ SSet.ι₀ := rfl
    rw [← Category.assoc, h, Category.assoc, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathHomotopy _).h₀,
      unitComparisonFiberPath_start]
    rfl
  h₁ := by
    have h : SSet.ι₁ ≫ (unitComparisonFiberPath η x w ▷ (Δ[1] : SSet.{u})) =
        unitComparisonFiberPath η x w ≫ SSet.ι₁ := rfl
    rw [← Category.assoc, h, Category.assoc, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.equivalencePathHomotopy _).h₁,
      unitComparisonFiberPath_end]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaArrowFamily_eq_const G x w _).symm
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro a
    exact False.elim a.1.property

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
