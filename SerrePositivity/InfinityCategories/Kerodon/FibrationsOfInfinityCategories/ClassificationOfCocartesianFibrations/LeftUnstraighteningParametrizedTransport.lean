module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.ParametrizedFiberTransportNaturality
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningFiberFamily

/-!
概要：unstraightening の写像空間比較の各対象での作用を普遍的なパラメーター付き輸送と比較する。
方針：既存の持ち上げを結合子で輸送族に直し、全写像空間での選択独立性を使う。
規約：既存の比較射や持ち上げを変更しない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、Lemma 5.6.9.1（Tag 02SN） の写像空間比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 概要：係数とパラメーターの積の prism の端点は結合子を通して元の係数の端点となる。
方針：三成分を各次数で計算する。
規約：区間を第一因子、係数を第二因子、パラメーターを第三因子に取る。
使われ方：既存の持ち上げを輸送族の標準の結合順へ直す。 -/
lemma fiberTransportFamily_reassociate_endpoint (A L : SSet.{u}) (i : Fin 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (A ⊗ L) ≫ (α_ (Δ[1] : SSet.{u}) A L).inv =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.simplexPrismVertex 1 i A ▷ L := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：結合子を通して係数を忘れるとパラメーターへの射影になる。
方針：三成分の射影を各次数で比較する。
規約：区間とパラメーターの二因子を残す。
使われ方：unstraightening の持ち上げの底の式を輸送族の条件へ移す。 -/
lemma fiberTransportFamily_reassociate_base (A L : SSet.{u}) :
    (α_ (Δ[1] : SSet.{u}) A L).inv ≫ (fst (Δ[1] : SSet.{u}) A ▷ L) =
      Δ[1] ◁ snd A L := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 概要：unstraightening の写像空間比較の fiber での作用は輸送族の終点である。
方針：既存の始点・終点・底の式を結合子で同じ表示へ直す。
規約：全ての coherent な変換の高次パラメーターを保持する。
使われ方：選択済み比較射と普遍的な輸送射の全次数の同定。 -/
noncomputable def leftUnstraighteningFiberTransportFamily {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FiberTransportFamily (b := G.app _ b) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection
      (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (F.app _ b)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b) where
  endpoint := uncurry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom F G b)
  prism := (α_ (Δ[1] : SSet.{u + 1}) _ _).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberFamilyLift F G b
  start := by
    rw [← Category.assoc, fiberTransportFamily_reassociate_endpoint,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberFamilyLift_start, Category.id_comp]
  finish := by
    rw [← Category.assoc, fiberTransportFamily_reassociate_endpoint]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberFamilyLift_end F G b).symm
  over_base := by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningFiberFamilyLift_projection,
      ← Category.assoc, ← Category.assoc, fiberTransportFamily_reassociate_base, Category.assoc]

/-- 概要：unstraightening の輸送族を curry すると元の写像空間比較の fiber 作用を回収する。
方針：curry と uncurry の往復を使う。
規約：射の厳密な等式。
使われ方：既存の比較射を輸送の族の選択独立性へ渡す。 -/
lemma leftUnstraighteningFiberTransportFamily_map {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (b : B _⦋0⦌) :
    (leftUnstraighteningFiberTransportFamily F G b).map =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom F G b := curry_uncurry _

/-- 概要：写像空間比較を対象 b で評価した作用は、評価後の普遍的な輸送と関手同型。
方針：輸送族を同じ底の族を持つ普遍輸送の引き戻しと比較する。
規約：全写像空間からの二つの実際の射を一つの関手同型で結ぶ。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、普遍輸送の局所的同値性を写像空間比較へ渡す。 -/
noncomputable def leftUnstraighteningMappingFiberHom_parametrizedIso {B : SSet.{u + 1}}
    (F G : B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingFiberHom F G b)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingPostOfEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt b) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex b F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex b G) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection (F.app _ b) (G.app _ b)) := by
  have h := (leftUnstraighteningFiberTransportFamily F G b).mapIso_parametrized
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection _
    (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_zero, SSet.const_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex])
    (by rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_one, SSet.const_comp,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt_functorVertex])
  rw [leftUnstraighteningFiberTransportFamily_map] at h
  exact h

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
