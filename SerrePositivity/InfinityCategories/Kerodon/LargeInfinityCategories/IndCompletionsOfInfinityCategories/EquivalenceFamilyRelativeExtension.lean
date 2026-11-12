module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeInternalHomLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceCylinderFunctorIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.RelativeEquivalenceCylinder
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.FunctorFiber
/-!
概要：指定部分の可逆円柱を、標的への元の像を厳密に保って延長する。
方針：相対内部 Hom の右持ち上げ性を可逆区間の端点へ適用する。
規約：元の部分図式と元の標的全図式を保持し、充填性を追加仮定にしない。
使われ方：指定始点評価の下で全余錐の比較を相対反映する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
/-- 概要：可逆な部分図式の修正を、元の標的全図式の下で厳密に延長する。
方針：相対内部 Hom の可逆区間持ち上げを使う。規約：全固定条件を保持。使われ方：相対反映。 -/
lemma exists_extension_of_equivalenceFamily_over
    {A B D E : SSet.{u}} (p : D ⟶ E) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (i : A ⟶ B) [Mono i] (u : B ⟶ D) (v : A ⟶ D)
    (V : A ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ⟶ D)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A false ≫ V = i ≫ u)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A true ≫ V = v)
    (hV : V ≫ p = fst A _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ≫ i ≫ u ≫ p) :
    ∃ F : B ⟶ D, i ≫ F = v ∧ F ≫ p = u ≫ p := by
  let t := Functor.PullbackObjObj.ofHasPullback internalHom i p
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting t.π := by
    intro A' B' j hm hj
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting.relativeInternalHom hp i t j hm hj
  have hbase : curry V ≫ (ihom A).map p =
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (u ≫ p))) ≫ (pre i).app E := by
    apply uncurry_injective
    rw [uncurry_natural_right, uncurry_curry, hV, uncurry_pre_app,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.uncurry_const_functorVertex]
    rw [← Category.assoc (i ▷ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval) (fst B _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval),
      whiskerRight_fst]
    rfl
  let P : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ⟶ t.pt := t.isPullback.lift
    (curry V) (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (u ≫ p))) hbase
  have hPf : P ≫ t.fst = curry V := t.isPullback.lift_fst _ _ _
  have hPs : P ≫ t.snd = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (u ≫ p)) :=
    t.isPullback.lift_snd _ _ _
  have he (b : Bool) : (curry V).app (Opposite.op ⦋0⦌)
      (nerveEquiv.symm (Codiscrete.mk (ULift.up b))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint A b ≫ V) := by
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.functorVertex_equivalenceCylinderEndpoint_uncurry (curry V) b
    rw [uncurry_curry] at h
    exact h.symm
  have tf : t.π ≫ t.fst = (pre i).app D := by
    convert t.π_fst using 1
    rfl
  have ts : t.π ≫ t.snd = (ihom B).map p := by
    convert t.π_snd using 1
    rfl
  have he₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint false ≫ curry V =
      (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (i ≫ u)) : 𝟙_ SSet.{u} ⟶ (ihom A).obj D) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint, SSet.const_comp]
    exact congrArg (fun z => (SSet.const z : 𝟙_ SSet.{u} ⟶ (ihom A).obj D))
      ((he false).trans (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex h₀))
  have hs : CommSq (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex u) : 𝟙_ SSet.{u} ⟶ (ihom B).obj D)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint false) t.π P := by
    constructor
    apply t.hom_ext
    · rw [Category.assoc, tf, Category.assoc, hPf, he₀, SSet.const_comp]
      rfl
    · rw [Category.assoc, ts, Category.assoc, hPs, SSet.comp_const, SSet.const_comp]
      rfl
  have := ht (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceIntervalPoint false) inferInstance
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_equivalenceIntervalPoint false)
  let G := hs.lift
  have hGf : G ≫ (pre i).app D = curry V := by
    rw [← tf, ← Category.assoc, hs.fac_right, hPf]
  have hGs : G ≫ (ihom B).map p = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (u ≫ p)) := by
    rw [← ts, ← Category.assoc, hs.fac_right, hPs]
  let z : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval.{u} _⦋0⦌ := nerveEquiv.symm (Codiscrete.mk (ULift.up true))
  obtain ⟨F, hF⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv B D).surjective (G.app (Opposite.op ⦋0⦌) z)
  refine ⟨F, ?_, ?_⟩
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hGf (Opposite.op ⦋0⦌)) z
    change ((pre i).app D).app _ (G.app (Opposite.op ⦋0⦌) z) = _ at h
    rw [← hF, he, h₁] at h
    exact h
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex_injective
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app hGs (Opposite.op ⦋0⦌)) z
    change ((ihom B).map p).app _ (G.app (Opposite.op ⦋0⦌) z) = _ at h
    rw [← hF] at h
    change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (F ≫ p) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (u ≫ p)) 0 at h
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using h
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
