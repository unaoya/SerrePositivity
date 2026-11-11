module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedSections
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.BousfieldKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.TowerDiagramExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceRightKan
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.PushoutProduct

/-!
概要：fibration の塔に値を持つ重み付き end の Kan 性。
方針：パラメーター付き自然変換のホーンを各段の相対持ち上げで整合的に充填する。
規約：重みは任意でよい。零段の Kan 性と隣接遷移の fibration 性を使う。
使われ方：Kerodon 7.5.3（Tag 03AP）、7.5.4（Tag 03B5）、γ3 の塔の homotopy 極限模型。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：各成分が anodyne な図式の射に沿って、fibration の塔への自然変換を延長できる。
方針：零段を Kan 性で持ち上げ、後続段を遷移の fibration 性で相対的に持ち上げる。
規約：射の成分ごとの anodyne 性は実際の全 fibration に対する持ち上げ性。
使われ方：Kerodon 7.5.3（Tag 03AP）、重みの変更による切断空間の比較。 -/
lemma exists_resized_tower_extension_of_anodyne
    {A B H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u}} (j : A ⟶ B)
    (hj : ∀ i, anodyneExtensions (j.app i))
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))]
    (a : A ⟶ H) : ∃ b : B ⟶ H, j ≫ b = a := by
  have (n : ℕ) : HasLiftingProperty (j.app (AsSmall.up.obj (Opposite.op (n + 1))))
      (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) :=
    hj _ _ ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
  have : HasLiftingProperty (j.app (AsSmall.up.obj (Opposite.op 0)))
      (terminal.from (H.obj (AsSmall.up.obj (Opposite.op 0)))) :=
    hj _ _ ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
  let sq : CommSq (a.app (AsSmall.up.obj (Opposite.op 0)))
      (j.app (AsSmall.up.obj (Opposite.op 0)))
      (terminal.from (H.obj (AsSmall.up.obj (Opposite.op 0))))
      (terminal.from (B.obj (AsSmall.up.obj (Opposite.op 0)))) := ⟨terminal.hom_ext _ _⟩
  obtain ⟨b, hb, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_resized_tower_diagram_extension j a sq.lift sq.fac_left
  exact ⟨b, hb⟩

/-- 概要：fibration の塔の重み付き切断空間から零段の内部 Hom への射影は fibration。
方針：指定された零段のホーン充填を保ち、後続段で重みとの直積のホーンを相対充填する。
規約：零段の Kan 性はこの相対的な主張には不要。
使われ方：Kerodon 7.5.3（Tag 03AP）、塔の homotopy 極限模型の相対的な充填。 -/
lemma weightedSections_tower_projection_fibration (W H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u})
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    Fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H (AsSmall.up.obj (Opposite.op 0))) := by
  rw [SSet.modelCategoryQuillen.fibration_iff]
  intro A B j hj
  simp only [J, MorphismProperty.iSup_iff] at hj
  obtain ⟨n, ⟨i⟩⟩ := hj
  constructor
  intro σ f₀ sq
  let U := W ⊗ (Functor.const (AsSmall.{u} ℕᵒᵖ)).obj (horn (n + 1) i : SSet.{u})
  let V := W ⊗ (Functor.const (AsSmall.{u} ℕᵒᵖ)).obj (Δ[n + 1] : SSet.{u})
  let j : U ⟶ V := W ◁ (Functor.const (AsSmall.{u} ℕᵒᵖ)).map (horn (n + 1) i).ι
  let a : U ⟶ H := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry σ
  have (m : ℕ) : HasLiftingProperty (j.app (AsSmall.up.obj (Opposite.op (m + 1))))
      (H.map (AsSmall.up.map (homOfLE (Nat.le_succ m)).op)) := by
    have ha := (anodyneExtensions.horn_ι i).whiskerLeft
      (W.obj (AsSmall.up.obj (Opposite.op (m + 1))))
    exact ha _ ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)
  have h₀ : j.app (AsSmall.up.obj (Opposite.op 0)) ≫ uncurry f₀ =
      a.app (AsSmall.up.obj (Opposite.op 0)) := by
    change (W.obj (AsSmall.up.obj (Opposite.op 0)) ◁ (horn (n + 1) i).ι) ≫
      uncurry f₀ = _
    rw [← uncurry_natural_left, ← sq.w]
    rfl
  obtain ⟨b, hb, hb₀⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_resized_tower_diagram_extension j a (uncurry f₀) h₀
  refine CommSq.HasLift.mk' { l := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift b, fac_left := ?_, fac_right := ?_ }
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv W H (horn (n + 1) i : SSet.{u})).injective
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry ((horn (n + 1) i).ι ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift b) = a
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsUncurry_lift]
    exact hb
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift_π, hb₀, curry_uncurry]

/-- 概要：fibration の塔に値を持つ任意の重み付き切断空間は Kan 複体。
方針：ホーンをパラメーター付き自然変換へ移し、零段で充填してから塔に沿って延長する。
規約：添字を係数の宇宙へ持ち上げ、重みに Kan 性や可縮性を要求しない。
使われ方：Kerodon 7.5.3（Tag 03AP）、7.5.4.6（Tag 03BB） の塔の end の Kan 性。 -/
lemma weightedSections_tower_kanComplex (W H : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u})
    [KanComplex (H.obj (AsSmall.up.obj (Opposite.op 0)))]
    [∀ n : ℕ, Fibration (H.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op))] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H) := by
  have := weightedSections_tower_projection_fibration W H
  exact isFibrant_of_fibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsπ W H (AsSmall.up.obj (Opposite.op 0)))

/-- 概要：零段が Kan で遷移が fibration の塔の Bousfield–Kan 型の end は Kan 複体。
方針：添字を AsSmall で持ち上げ、Bousfield–Kan の重みに一般の重み付き塔の充填を適用する。
規約：標準比較射の同値性はこの補題の結論に含めない。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、γ3c の塔の homotopy 極限の比較先。 -/
lemma bousfieldKanHolim_tower_kanComplex (H : ℕᵒᵖ ⥤ SSet.{u})
    [KanComplex (H.obj (Opposite.op 0))]
    [∀ n : ℕ, Fibration (H.map (homOfLE (Nat.le_succ n)).op)] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanHolim ((AsSmall.down : AsSmall.{u} ℕᵒᵖ ⥤ ℕᵒᵖ) ⋙ H)) := by
  let H' : AsSmall.{u} ℕᵒᵖ ⥤ SSet.{u} := AsSmall.down ⋙ H
  have : KanComplex (H'.obj (AsSmall.up.obj (Opposite.op 0))) :=
    inferInstanceAs (KanComplex (H.obj (Opposite.op 0)))
  have (n : ℕ) : Fibration (H'.map (AsSmall.up.map (homOfLE (Nat.le_succ n)).op)) :=
    inferInstanceAs (Fibration (H.map (homOfLE (Nat.le_succ n)).op))
  exact weightedSections_tower_kanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight (AsSmall.{u} ℕᵒᵖ)) H'

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
