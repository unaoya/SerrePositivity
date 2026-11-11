module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeEquivalencePathAt
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.VertexDiscrete

/-!
概要：同じ制限を保つ全図式族を、全入力頂点で指定した図式へ移す。
方針：制限の相対可逆 path の自明 Kan 性を、入力の零骨格へ適用する。
規約：指定された全 path 自体を回収する。辺や頂点だけの比較へ弱めない。
使われ方：D-8 e の元の選択四角形・P 比較への厳密な復帰。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories

/-- 全入力上で指定部分を固定し、各入力で選んだ全可逆 path を厳密に回収する。 -/
lemma nativeDiagramFamily_relativeReplacement {A B K X : SSet.{u}}
    [Quasicategory X] (i : A ⟶ B) [Mono i]
    (F : K ⟶ (ihom B).obj X)
    (a : K _⦋0⦌ → (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom B).obj X)) _⦋0⦌)
    (ha : ∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X)).app (Opposite.op ⦋0⦌) (a k) =
      ((F ≫ (pre i).app X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl ((ihom A).obj X)).app
        (Opposite.op ⦋0⦌) k)
    (hf : ∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom B).obj X) 1).app
      (Opposite.op ⦋0⦌) (a k) = F.app (Opposite.op ⦋0⦌) k) :
    ∃ L : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom B).obj X),
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X) =
        (F ≫ (pre i).app X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl ((ihom A).obj X) ∧
      L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom B).obj X) 1 = F ∧
      ∀ k, L.app (Opposite.op ⦋0⦌) k = a k := by
  let p := (pre i).app X
  let P := (F ≫ p) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl ((ihom A).obj X)
  have hP : P ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom A).obj X) 1 = F ≫ p := by
    simp only [P, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint, Category.comp_id]
  let t : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathTargetAt p 1 := pullback.lift P F hP
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p 1) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_relativeEquivalencePathMapAt_pre i X 1
  have : HasLiftingProperty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι K) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p 1) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem _ inferInstance
  let sq : CommSq (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap a) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteι K)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt p 1) t := by
    constructor
    apply pullback.hom_ext
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_fst,
        Category.assoc, pullback.lift_fst]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap_comp _ P a ha
    · rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_snd,
        Category.assoc, pullback.lift_snd]
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.vertexDiscreteMap_comp _ F a hf
  refine ⟨sq.lift, ?_, ?_, ?_⟩
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_fst p 1, ← Category.assoc, sq.fac_right]
    exact pullback.lift_fst _ _ _
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.relativeEquivalencePathMapAt_snd p 1, ← Category.assoc, sq.fac_right]
    exact pullback.lift_snd _ _ _
  · intro k
    have hk := ConcreteCategory.congr_hom
      (NatTrans.congr_app sq.fac_left (Opposite.op ⦋0⦌)) k
    change sq.lift.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant k 0) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (a k) 0 at hk
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using hk

/-- 同じ全図式族の制限を保ち、各入力での全図式を指定値へ厳密に移す。 -/
lemma nativeDiagramFamily_exists_replacement {A B K X : SSet.{u}}
    [Quasicategory X] (i : A ⟶ B) [Mono i]
    (F : K ⟶ (ihom B).obj X)
    (a : K _⦋0⦌ → (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePath ((ihom B).obj X)) _⦋0⦌)
    (ha : ∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap ((pre i).app X)).app (Opposite.op ⦋0⦌) (a k) =
      ((F ≫ (pre i).app X) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl ((ihom A).obj X)).app
        (Opposite.op ⦋0⦌) k)
    (hf : ∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom B).obj X) 1).app
      (Opposite.op ⦋0⦌) (a k) = F.app (Opposite.op ⦋0⦌) k) :
    ∃ G : K ⟶ (ihom B).obj X,
      G ≫ (pre i).app X = F ≫ (pre i).app X ∧
      ∀ k, G.app (Opposite.op ⦋0⦌) k =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint ((ihom B).obj X) 0).app (Opposite.op ⦋0⦌) (a k) := by
  obtain ⟨L, hL, hF, hv⟩ := nativeDiagramFamily_relativeReplacement i F a ha hf
  refine ⟨L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0, ?_, ?_⟩
  · rw [Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathMap_endpoint, ← Category.assoc, hL]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathRefl_endpoint, Category.comp_id]
  · intro k
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalencePathEndpoint _ 0).app _ (L.app _ k) = _
    rw [hv]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
