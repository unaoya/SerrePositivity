module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ReflectedConeLimitLift
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanLimits

/-!
概要：元の錐の Bousfield–Kan 比較と反転した錐の比較の同値性を照合する。
方針：両比較を厳密極限への射と標準比較の合成に分解し、反転の極限保存を使う。
規約：錐が厳密極限であることを仮定しない。三形状で標準比較の同値性を検証する。
使われ方：HTT 4.2.4.1 の限定形、γ3b の元の q_x と q′ の橋渡し。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
noncomputable section

local instance : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor

/-- 概要：任意の錐の標準比較は厳密極限への射と極限からの標準比較の合成。
方針：錐の比較の自然性に極限への持ち上げと恒等自然変換を渡す。
規約：錐の極限性や Kan 性を要求しない。
使われ方：元の比較と反転した比較を中間の厳密極限で照合する。 -/
lemma bousfieldKanConeComparison_limitLift {I : Type u} [SmallCategory I]
    {H : I ⥤ SSet.{u}} (c : Cone H) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c = limit.lift H c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) c (limit.cone H)
    (limit.lift H c) (𝟙 H) (fun i ↦ by
      change limit.lift H c ≫ limit.π H i = c.π.app i ≫ 𝟙 (H.obj i)
      rw [limit.lift_π, Category.comp_id])
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) c =
    limit.lift H c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I) (limit.cone H)
  simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_id, Category.comp_id] using h.symm

/-- 概要：終対象の重みの切断が Kan なら厳密極限も Kan。
方針：終対象の重みの比較同型で Kan 性を移す。
規約：重み W とその終対象性を明示し、錐の頂点を別に仮定しない。
使われ方：cospan と塔の厳密極限を同値性の消去則に渡す。 -/
lemma strictLimit_kanComplex_of_terminalWeight {I : Type u} [SmallCategory I]
    (W H : I ⥤ SSet.{u}) (hW : IsTerminal W) [KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H)] :
    KanComplex (limit H) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_isIso_of_isTerminalWeight W hW (limit.cone H) (limit.isLimit H)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W (limit.cone H))).symm

/-- 概要：元と反転後の極限標準比較が同値なら任意の Kan な錐の比較の同値性も一致する。
方針：厳密極限への射の反転比較と、両標準比較の同値性の消去則を使う。
規約：標準比較の同値性は二つとも明示し、錐自体の極限性は要求しない。
使われ方：指定三形状の実際の q_x と q′ の同値判定の共通部分。 -/
lemma bousfieldKanConeComparison_reflection_iff
    {I : Type u} [SmallCategory I] {H : I ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)] [KanComplex (limit H)]
    (hκ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H))
    (hκ' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison (H ⋙ SSet.opFunctor))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) := by
  have : ∀ i, KanComplex ((H ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (H.obj i).op)
  have : KanComplex (limit (H ⋙ SSet.opFunctor)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanComplex_of_iso (preservesLimitIso SSet.opFunctor H)
  have : KanComplex (SSet.opFunctor.mapCone c).pt :=
    inferInstanceAs (KanComplex c.pt.op)
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex H
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim_kanComplex (H ⋙ SSet.opFunctor)
  rw [bousfieldKanConeComparison_limitLift c,
    bousfieldKanConeComparison_limitLift (SSet.opFunctor.mapCone c)]
  constructor
  · intro h
    exact ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ReflectedConeLimitLift.reflectedConeLimitLift_homotopyEquivalence_iff c).mpr (hκ.cancel_right h)).comp hκ'
  · intro h
    exact ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.ReflectedConeLimitLift.reflectedConeLimitLift_homotopyEquivalence_iff c).mp (hκ'.cancel_right h)).comp hκ

/-- 概要：離散 Kan 図式の任意の Kan な錐の比較の同値性は反転で変わらない。
方針：元と反転後の離散標準比較の同型性を一般の判定へ渡す。
規約：添字の有限性や錐の厳密極限性は要求しない。
使われ方：γ3b の積の q_x と q′ の照合。 -/
lemma bousfieldKanConeComparison_reflection_discrete_iff {J : Type u}
    {H : Discrete J ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) := by
  exact bousfieldKanConeComparison_reflection_iff c
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_discrete_homotopyEquivalence H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_discrete_homotopyEquivalence (H ⋙ SSet.opFunctor))

/-- 概要：一脚 fibration の Kan cospan の任意の Kan な錐の比較の同値性は反転で変わらない。
方針：終対象重みの切断で厳密極限の Kan 性を証明し、両標準比較の同値性を使う。
規約：右脚の fibration 性や錐の厳密極限性は要求しない。
使われ方：γ3b の引き戻しの q_x と q′ の照合。 -/
lemma bousfieldKanConeComparison_reflection_cospan_iff
    {H : AsSmall.{u} WalkingCospan ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    [Fibration (H.map (AsSmall.up.map WalkingCospan.Hom.inl))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) := by
  let U := (Functor.const (AsSmall.{u} WalkingCospan)).obj (Δ[0] : SSet.{u})
  have : Mono (U.map (AsSmall.up.map WalkingCospan.Hom.inr)) := by
    change Mono (𝟙 (Δ[0] : SSet.{u}))
    infer_instance
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections U H) := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections_cospan_leftFibration_kanComplex U H
  have : KanComplex (limit H) := strictLimit_kanComplex_of_terminalWeight U H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightIsTerminalOfObj U (fun _ ↦ stdSimplex.isTerminalObj₀))
  have : ∀ i, KanComplex ((H ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (H.obj i).op)
  have : Fibration ((H ⋙ SSet.opFunctor).map (AsSmall.up.map WalkingCospan.Hom.inl)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.fibration_opFunctor_map _
  exact bousfieldKanConeComparison_reflection_iff c
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence H
      (limit.cone H) (limit.isLimit H))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison_cospan_leftFibration_homotopyEquivalence (H ⋙ SSet.opFunctor)
      (limit.cone _) (limit.isLimit _))

/-- 概要：Kan fibration の塔の任意の Kan な錐の比較の同値性は反転で変わらない。
方針：終対象重みの切断で厳密極限の Kan 性を証明し、両標準比較の同値性を使う。
規約：隣接遷移の fibration 性を要求し、錐の厳密極限性は要求しない。
使われ方：γ3b の塔の q_x と q′ の照合。 -/
lemma bousfieldKanConeComparison_reflection_tower_iff
    {H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (c : Cone H)
    [KanComplex c.pt] [∀ i, KanComplex (H.obj i)]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison c) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanConeComparison (SSet.opFunctor.mapCone c)) := by
  let U := (Functor.const (AsSmall.{u} ℕᵒᵖ)).obj (Δ[0] : SSet.{u})
  have : KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections U H) := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.weightedSections_tower_kanComplex U H
  have : KanComplex (limit H) := strictLimit_kanComplex_of_terminalWeight U H
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightIsTerminalOfObj U (fun _ ↦ stdSimplex.isTerminalObj₀))
  have : ∀ i, KanComplex ((H ⋙ SSet.opFunctor).obj i) :=
    fun i ↦ inferInstanceAs (KanComplex (H.obj i).op)
  have : ∀ n : ℕ, Fibration ((H ⋙ SSet.opFunctor).map
      (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) := fun _ ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.fibration_opFunctor_map _
  exact bousfieldKanConeComparison_reflection_iff c
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_tower_homotopyEquivalence H)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison_tower_homotopyEquivalence (H ⋙ SSet.opFunctor))

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
