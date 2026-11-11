module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanConeLimits
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：Kan fibration の可算塔の実際の極限を 𝒮 の極限錐として公開する。
方針：台の塔の極限の Kan 性で錐を束縛し、全 Hom の極限性と遷移の fibration 性を検証する。
規約：添字は AsSmall ℕᵒᵖ、元の小さな塔の strict 極限を使う。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB）、γ3c と F2 の塔の極限。

対応節は Kerodon 7.6（Tag 03E8）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits

variable (F : AsSmall.{u} ℕᵒᵖ ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})

/-- 概要：Kan 複体の塔の台の単体集合の標準極限錐。
方針：元の可算添字へ降ろした塔の極限錐を AsSmall の添字へ戻す。
規約：頂点は limit (AsSmall.up ⋙ F ⋙ kanObjectForget)。
使われ方：Kerodon 7.5.3.12（Tag 03B1） の実際の塔の極限の普遍性。 -/
noncomputable def kanTowerUnderlyingCone : Cone (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) :=
  (limit.cone (AsSmall.up ⋙ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).whisker AsSmall.down

variable [∀ n : ℕ, Fibration (show
  (F.obj (AsSmall.up.obj (Opposite.op (n + 1)))).obj ⟶
    (F.obj (AsSmall.up.obj (Opposite.op n))).obj from
      F.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))]

/-- 概要：Kan fibration の塔の標準極限錐の頂点は Kan 複体。
方針：元の可算添字での塔の Kan 性の定理へ各段と遷移を渡す。
規約：追加の極限対象の Kan 性を仮定しない。
使われ方：Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB） の塔の頂点の束縛。 -/
lemma kanTowerUnderlyingCone_kanComplex : KanComplex (kanTowerUnderlyingCone F).pt := by
  have : KanComplex ((AsSmall.up ⋙ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).obj (Opposite.op 0)) :=
    inferInstanceAs (KanComplex (F.obj (AsSmall.up.obj (Opposite.op 0))).obj)
  have : ∀ n : ℕ, Fibration ((AsSmall.up ⋙ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget).map
      (homOfLE (Nat.le_succ n)).op) := fun n ↦ by
    change Fibration (show (F.obj (AsSmall.up.obj (Opposite.op (n + 1)))).obj ⟶
      (F.obj (AsSmall.up.obj (Opposite.op n))).obj from
        F.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.towerLimit_kanComplex (AsSmall.up ⋙ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)

/-- 概要：Kan fibration の塔の極限の頂点を束縛した通常の Kan 複体の錐。
方針：台の標準極限錐の頂点の Kan 性で束縛する。
規約：射影は元の strict 極限の射影そのもの。
使われ方：HTT 4.2.4.1 の γ3c の実際の塔の錐の入力。 -/
noncomputable def kanTowerCone : Cone F :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectConeOfUnderlying F (kanTowerUnderlyingCone F) (kanTowerUnderlyingCone_kanComplex F)

/-- 概要：束縛した塔の錐の台の頂点は実際の塔の strict 極限。
方針：束縛した頂点の定義を計算する。
規約：単体集合の厳密な等号。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の 𝒮 の極限対象の明示。 -/
lemma kanTowerCone_obj : (kanTowerCone F).pt.obj =
    limit (AsSmall.up ⋙ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget) := rfl

/-- 概要：束縛した塔の錐は忘却後に標準極限の普遍性を持つ。
方針：元の可算塔の普遍性を AsSmall の圏同値で移して束縛する。
規約：Hom 錐の極限性を追加仮定にしない。
使われ方：HTT 4.2.4.1 の全 Hom の極限条件の検証。 -/
noncomputable def kanTowerCone_forget_isLimit :
    IsLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget.mapCone (kanTowerCone F)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectConeOfUnderlying_forget_isLimit
  exact (limit.isLimit (AsSmall.up ⋙ F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)).whiskerEquivalence
    (AsSmall.equiv : ℕᵒᵖ ≌ AsSmall.{u} ℕᵒᵖ).symm

/-- 概要：束縛した塔の錐は通常の Kan 複体の圏でも極限錐。
方針：台の単体集合での普遍性を Kan 複体の射へ戻す。
規約：全隣接遷移の台の fibration 性のみを要求する。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の ∞ 極限へ移す実際の strict な塔の極限。 -/
noncomputable def kanTowerCone_isLimit : IsLimit (kanTowerCone F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectCone_isLimit_of_forget _ (kanTowerCone_forget_isLimit F)

/-- 概要：𝒮 の既存の塔の図式上の実際の極限錐。
方針：Kan 複体の塔の錐を coherent nerve に写し、F1 の図式に同定する。
規約：頂点の台は元の可算塔の strict 極限。
使われ方：HTT 4.2.4.1 の双対、γ3c と F2 の fibration の塔の極限。 -/
noncomputable def spaceTowerCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve F) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (kanTowerCone F)).cast (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram_eq_kanDiagram F)

/-- 概要：Kan fibration の可算塔の実際の極限は 𝒮 の極限錐となる。
方針：全 Hom の極限性と遷移の fibration 性を検証して塔の移送定理を適用する。
規約：Hom 条件や追加の比較同値を仮定しない。
使われ方：HTT 4.2.4.1 の双対、Kerodon 7.5.3.12（Tag 03B1）、7.5.4.6（Tag 03BB）、γ3c の具体的な塔の極限。 -/
@[kerodon 03HU]
lemma spaceTowerCone_isLimitCone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (spaceTowerCone F) := by
  have : ∀ (X : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (n : ℕ), Fibration
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.simplicialHomDiagram F X).map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) :=
    fun X n ↦ by
      change Fibration (((SimplicialCategory.sHomFunctor _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}).obj
        (Opposite.op X)).map (F.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)))
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHom_map_fibration X _
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone.cast
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.strictCoherentCone_isLimit_of_tower_homLimit (kanTowerCone F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.kanObjectHomCone_isLimit_of_forget _ (kanTowerCone_forget_isLimit F))

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits
