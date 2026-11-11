module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.DiscreteComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.TowerExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan

/-!
概要：Kan 複体の積と fibration による引き戻し・逆向きの塔の strict 極限の Kan 性。
方針：積は成分ごと、引き戻しと塔は相対的にホーンを充填する。
規約：モデル構造の存在や弱同値を使わず、Fibration は全ホーンの持ち上げ性として使う。
使われ方：Kerodon 7.5.3（Tag 03AP）、7.5.4（Tag 03B5）、γ3c の strict な極限の前提の検証。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

/-- 概要：Kan 性は単体集合の同型で移せる。
方針：ホーンを逆同型で戻して充填し、順方向へ写す。
規約：任意の厳密な同型を扱う。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、strict 極限と homotopy 極限模型の同型。 -/
lemma kanComplex_of_iso {X Y : SSet.{u}} [KanComplex X] (e : X ≅ Y) : KanComplex Y := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
  intro n i _ σ
  obtain ⟨F, hF⟩ := KanComplex.hornFilling (σ ≫ e.inv)
  refine ⟨F ≫ e.hom, ?_⟩
  rw [← Category.assoc, ← hF, Category.assoc, e.inv_hom_id, Category.comp_id]

/-- 概要：Kan 図式の離散 strict 極限は Kan 複体。
方針：全ての成分のホーンを充填し、離散図式の錐から極限へ持ち上げる。
規約：任意の小さな積と空積を含む。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、γ3c の有限積の Kan 性。 -/
instance discreteLimit_kanComplex {J : Type u} (H : Discrete J ⥤ SSet.{u})
    [∀ i, KanComplex (H.obj i)] : KanComplex (limit H) := by
  classical
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
  intro n i _ σ
  have hf (j : Discrete J) : ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ H.obj j,
      (horn (n + 1) i).ι ≫ F = σ ≫ limit.π H j := by
    obtain ⟨F, hF⟩ := KanComplex.hornFilling (σ ≫ limit.π H j)
    exact ⟨F, hF.symm⟩
  choose f hf using hf
  let c : Cone H := ⟨Δ[n + 1], Discrete.natTrans f⟩
  refine ⟨limit.lift H c, ?_⟩
  apply limit.hom_ext
  intro j
  rw [Category.assoc, limit.lift_π]
  exact hf j

/-- 概要：離散 Kan 図式の Bousfield–Kan 型の end は Kan 複体。
方針：strict 極限からの実際の比較射が同型であることを使う。
規約：一般の図式の end の Kan 性はこの補題の主張に含めない。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、homotopy 積の具体的な模型。 -/
instance bousfieldKanHolim_discrete_kanComplex {J : Type u}
    (H : Discrete J ⥤ SSet.{u}) [∀ i, KanComplex (H.obj i)] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim H) :=
  kanComplex_of_iso (asIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanLimitComparison H))

/-- 概要：一方の脚が Kan fibration で、他方の始域が Kan なら引き戻しも Kan。
方針：他方の始域のホーンを充填してから、fibration の相対ホーンを持ち上げる。
規約：元の二つの他の対象に Kan 性を追加しない。
使われ方：Kerodon 7.5.4（Tag 03B5）、γ3c の fibration による引き戻し。 -/
lemma pullback_kanComplex_of_fibration {E B D : SSet.{u}} (p : E ⟶ B) (q : D ⟶ B)
    [Fibration p] [KanComplex D] : KanComplex (pullback p q) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
  intro n i _ σ
  obtain ⟨d, hd⟩ := KanComplex.hornFilling (σ ≫ pullback.snd p q)
  have : HasLiftingProperty (horn (n + 1) i).ι p :=
    (SSet.modelCategoryQuillen.fibration_iff p).1 inferInstance _ (horn_ι_mem_J _ i)
  let sq : CommSq (σ ≫ pullback.fst p q) (horn (n + 1) i).ι p (d ≫ q) := ⟨by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hd, Category.assoc]⟩
  refine ⟨pullback.lift sq.lift d sq.fac_right, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst]
    exact sq.fac_left
  · rw [Category.assoc, pullback.lift_snd]
    exact hd.symm

/-- 概要：零段が Kan で各遷移が Kan fibration の逆向きの可算塔の strict 極限は Kan。
方針：零段でホーンを充填し、各遷移の相対持ち上げで整合的な全段の錐に延長する。
規約：零段以外の Kan 性を別の前提にはしない。
使われ方：Kerodon 7.5.3（Tag 03AP）、γ3c の fibration の塔の strict 極限。 -/
lemma towerLimit_kanComplex (H : ℕᵒᵖ ⥤ SSet.{u}) [KanComplex (H.obj (Opposite.op 0))]
    [∀ n : ℕ, Fibration (H.map (homOfLE (Nat.le_succ n)).op)] : KanComplex (limit H) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
  intro n i _ σ
  have (m : ℕ) : HasLiftingProperty (horn (n + 1) i).ι
      (H.map (homOfLE (Nat.le_succ m)).op) :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance _ (horn_ι_mem_J _ i)
  let a : (Functor.const ℕᵒᵖ).obj (horn (n + 1) i : SSet.{u}) ⟶ H :=
    (Functor.const ℕᵒᵖ).map σ ≫ (limit.cone H).π
  obtain ⟨f₀, h₀⟩ := KanComplex.hornFilling (a.app (Opposite.op 0))
  obtain ⟨b, hb, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_tower_extension H (horn (n + 1) i).ι a f₀ h₀.symm
  refine ⟨limit.lift H ⟨Δ[n + 1], b⟩, ?_⟩
  apply limit.hom_ext
  intro m
  rw [Category.assoc, limit.lift_π]
  exact congrArg (fun η ↦ η.app m) hb

/-- 概要：Kan fibration の可算塔の極限の零段への射影も Kan fibration。
方針：各ホーンの持ち上げ性を零段への射影に移す一般の塔の延長を使う。
規約：零段の Kan 性はこの相対的な主張には不要。
使われ方：Kerodon 7.5.3（Tag 03AP）、γ3c の塔を相対的に計算する。 -/
lemma towerLimitπ_zero_fibration (H : ℕᵒᵖ ⥤ SSet.{u})
    [∀ n : ℕ, Fibration (H.map (homOfLE (Nat.le_succ n)).op)] :
    Fibration (limit.π H (Opposite.op 0)) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B j hj
  simp only [J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨i⟩⟩ := hj
  have (m : ℕ) : HasLiftingProperty (horn (n + 1) i).ι
      (H.map (homOfLE (Nat.le_succ m)).op) :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance _ (horn_ι_mem_J _ i)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.hasLiftingProperty_towerLimitπ_zero H (horn (n + 1) i).ι

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
