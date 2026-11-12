module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeFunctorCoreRestriction
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.RelativeFunctorCoreRestriction

public import SerrePositivity.KST.Fibration.FunctorCoreCriterion
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.SuspensionDiagramArrows
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePathReplacement

/-!
概要：全頂点を覆う制限に沿って、元の商の関手 core 逆像を厳密に回収する。
方針：全高次単体の core 所属を各頂点評価に戻し、元の制限の全境界充填を制限する。
規約：商の局所化同値や Hom の充満忠実性はこの制限射の RLP から推論しない。
使われ方：c5 の実有限図式の貼合せを、指定部分族を保って元の相対図式内で行う。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

/-- 全頂点を覆う実制限は、関手圏の core を全単体で反映する。 -/
lemma functorCore_eq_preimage_of_vertexSurjective {K L C : SSet.{u}} [Quasicategory C]
    (j : L ⟶ K) (hj : Function.Surjective (j.app (Opposite.op ⦋0⦌))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj C) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom L).obj C)).preimage ((pre j).app C) := by
  ext n s
  change s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj C)).obj n ↔
    ((pre j).app C).app n s ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom L).obj C)).obj n
  have he (l : L _⦋0⦌) : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) l).app n
      (((pre j).app C).app n s) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := C) (j.app (Opposite.op ⦋0⦌) l)).app n s :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.comp_app_congr (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.stable_pre_evaluateFunctorAt (X := C) j l) n s
  constructor
  · intro hs
    refine (functorCore_mem_iff (K := L) (C := C)
      (((pre j).app C).app n s)).2 (fun l => ?_)
    have hk := (functorCore_mem_iff (K := K) (C := C) s).1 hs
    exact (congrArg (fun v : C.obj n => v ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).obj n) (he l)).mpr (hk _)
  · intro hs
    refine (functorCore_mem_iff (K := K) (C := C) s).2 (fun k => ?_)
    obtain ⟨l, hl⟩ := hj k
    have hh := (functorCore_mem_iff (K := L) (C := C)
      (((pre j).app C).app n s)).1 hs l
    have hv := (congrArg (fun v : C.obj n => v ∈ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore C).obj n) (he l)).mp hh
    exact hl ▸ hv

instance relativeFunctorCore_quasicategory {B C : SSet.{u}} [Quasicategory B]
    [Quasicategory C] (q : B ⟶ C) (K : SSet.{u}) :
    Quasicategory (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q K : SSet.{u}) := by
  have he := relativeDiagram_eq_functorCore_preimage q (𝟙 ((ihom K).obj B))
  simp only [Category.id_comp] at he
  change Quasicategory ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom K).obj C)).preimage ((ihom K).map q) : SSet.{u})
  rw [← he]
  infer_instance

/-- 全頂点を覆う制限の下で、元の相対図式は同じ部分複体の厳密な逆像。 -/
lemma relativeFunctorCore_eq_preimage_of_vertexSurjective
    {K L B C : SSet.{u}} [Quasicategory C] (q : B ⟶ C)
    (j : L ⟶ K) (hj : Function.Surjective (j.app (Opposite.op ⦋0⦌))) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q K =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q L).preimage ((pre j).app B) := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore
  rw [functorCore_eq_preimage_of_vertexSurjective j hj, ← Subcomplex.preimage_comp,
    ← Subcomplex.preimage_comp, (pre j).naturality q]

/-- 元の全図式の制限を、同じ core 逆像の間の実射として保持する。 -/
def relativeFunctorCoreRestriction {K L B C : SSet.{u}} [Quasicategory C]
    (q : B ⟶ C) (j : L ⟶ K)
    (hj : Function.Surjective (j.app (Opposite.op ⦋0⦌))) :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q K : SSet.{u}) ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q L : SSet.{u}) :=
  Subcomplex.lift ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q K).ι ≫ (pre j).app B) (by
    rintro n _ ⟨s, rfl⟩
    have hs : s.val ∈ ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q L).preimage ((pre j).app B)).obj n := by
      rw [← relativeFunctorCore_eq_preimage_of_vertexSurjective q j hj]
      exact s.property
    exact hs)

@[reassoc]
lemma relativeFunctorCoreRestriction_ι {K L B C : SSet.{u}} [Quasicategory C]
    (q : B ⟶ C) (j : L ⟶ K)
    (hj : Function.Surjective (j.app (Opposite.op ⦋0⦌))) :
    relativeFunctorCoreRestriction q j hj ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q L).ι =
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q K).ι ≫ (pre j).app B := rfl

/-- 制限は元の商射そのものと、全単体写像として厳密に可換。 -/
lemma relativeFunctorCoreRestriction_quotient {K L B C : SSet.{u}} [Quasicategory C]
    (q : B ⟶ C) (j : L ⟶ K)
    (hj : Function.Surjective (j.app (Opposite.op ⦋0⦌))) :
    relativeFunctorCoreRestriction q j hj ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q L =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre j).app C) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom L).obj C)).ι).mp
  change relativeFunctorCoreRestriction q j hj ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q L).ι ≫ (ihom L).map q =
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCoreQuotient q K ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap ((pre j).app C) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore ((ihom L).obj C)).ι
  rw [← Category.assoc, relativeFunctorCoreRestriction_ι q j hj, Category.assoc,
    ← (pre j).naturality q, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreMap_ι, ← Category.assoc]
  rfl

/-- 指定部分族を固定し、同じ相対図式の制限に沿って全族を充填する。 -/
lemma exists_relative_relativeFunctorCoreRestriction
    {K L B C P Q : SSet.{u}} [Quasicategory C] (q : B ⟶ C)
    (j : L ⟶ K) (hj : Function.Surjective (j.app (Opposite.op ⦋0⦌)))
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre j).app B)] (i : P ⟶ Q) [Mono i]
    (a : P ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q K : SSet.{u}))
    (b : Q ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q L : SSet.{u}))
    (ha : a ≫ relativeFunctorCoreRestriction q j hj = i ≫ b) :
    ∃ F : Q ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q K : SSet.{u}),
      i ≫ F = a ∧ F ≫ relativeFunctorCoreRestriction q j hj = b := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration.mem (p := (pre j).app B) i inferInstance
  have hs : CommSq (a ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q K).ι) i ((pre j).app B)
      (b ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q L).ι) := by
    constructor
    rw [Category.assoc, ← relativeFunctorCoreRestriction_ι q j hj, ← Category.assoc, ha,
      Category.assoc]
  let L' := hs.lift
  let F : Q ⟶ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q K : SSet.{u}) := Subcomplex.lift L' (by
    rintro n _ ⟨s, rfl⟩
    rw [relativeFunctorCore_eq_preimage_of_vertexSurjective q j hj]
    have he := ConcreteCategory.congr_hom (C := Type u)
      (NatTrans.congr_app hs.fac_right n) s
    change ((pre j).app B).app n (L'.app n s) ∈ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q L).obj n
    change ((pre j).app B).app n (L'.app n s) = (b.app n s).val at he
    rw [he]
    exact (b.app n s).property)
  have hF : F ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q K).ι = L' := rfl
  refine ⟨F, ?_, ?_⟩
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q K).ι).mp
    rw [Category.assoc, hF]
    exact hs.fac_left
  · apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.relativeFunctorCore q L).ι).mp
    rw [Category.assoc, relativeFunctorCoreRestriction_ι q j hj, ← Category.assoc, hF]
    exact hs.fac_right

/-- 元の制限の全境界充填は、その同じ core 逆像の間でも成立する。 -/
instance relativeFunctorCoreRestriction_trivialKanFibration
    {K L B C : SSet.{u}} [Quasicategory C] (q : B ⟶ C)
    (j : L ⟶ K) (hj : Function.Surjective (j.app (Opposite.op ⦋0⦌)))
    [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration ((pre j).app B)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (relativeFunctorCoreRestriction q j hj) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary _).2
  intro n
  constructor
  intro a b sq
  obtain ⟨F, hl, hr⟩ := exists_relative_relativeFunctorCoreRestriction q j hj
    (boundary n).ι a b sq.w
  exact CommSq.HasLift.mk' ⟨F, hl, hr⟩

end SerrePositivity.KST.LocalizingInvariants
