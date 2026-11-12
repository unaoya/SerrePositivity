module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceRestriction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.EquivalenceTerminal
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ExcisionGridCoreDiagram
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismFilling
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.PosetClosureRetraction

/-!
概要：比較格子の穿孔 core と元の cospan の実極限を比較する。
方針：固定した初期収縮と標準ホーンの全単体同型を使う。
規約：一般安定性を仮定しない。使われ方：HA 1.4.2.15 の実 θ の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet MorphismProperty
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

lemma leftAnodyneExtensions_of_fixed_initial_homotopy {A B : SSet.{u}}
    (i : A ⟶ B) [Mono i] (r : B ⟶ A) (hir : i ≫ r = 𝟙 A)
    (J : (Δ[1] : SSet.{u}) ⊗ B ⟶ B)
    (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 B ≫ J = r ≫ i)
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B ≫ J = 𝟙 B)
    (hfix : (Δ[1] ◁ i) ≫ J = snd (Δ[1] : SSet.{u}) A ≫ i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions i := by
  let sq := Functor.PushoutObjObj.ofHasPushout (curriedTensor SSet.{u}) (horn 1 0).ι i
  have hw : ((horn 1 0).ι ▷ A) ≫ snd (Δ[1] : SSet.{u}) A =
      ((horn 1 0 : SSet.{u}) ◁ i) ≫ (snd (horn 1 0 : SSet.{u}) B ≫ r) := by
    rw [whiskerRight_snd, ← Category.assoc, whiskerLeft_snd, Category.assoc, hir,
      Category.comp_id]
  let q := sq.isPushout.desc (snd (Δ[1] : SSet.{u}) A)
    (snd (horn 1 0 : SSet.{u}) B ≫ r) hw
  have hqi : q ≫ i = sq.ι ≫ J := by
    apply sq.hom_ext
    · rw [← Category.assoc, sq.isPushout.inl_desc, ← Category.assoc, sq.inl_ι]
      exact hfix.symm
    · rw [← Category.assoc, sq.isPushout.inr_desc, ← Category.assoc, sq.inr_ι]
      change (snd (horn 1 0 : SSet.{u}) B ≫ r) ≫ i = ((horn 1 0).ι ▷ B) ≫ J
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization]
      simp only [Category.assoc, h₀]
  let t := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ sq.inl
  have ht : t ≫ sq.ι = i ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B := by
    rw [Category.assoc, sq.inl_ι]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality 1 i
  have htop : t ≫ q = 𝟙 A := by
    rw [Category.assoc, sq.isPushout.inl_desc]
    rfl
  let re : RetractArrow i sq.ι :=
    { i := Arrow.homMk' t (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 B) ht
      r := Arrow.homMk' q J hqi
      retract := by
        apply Arrow.hom_ext
        · exact htop
        · exact h₁ }
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.of_retract re
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions_pushoutObjObj_point i sq)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
