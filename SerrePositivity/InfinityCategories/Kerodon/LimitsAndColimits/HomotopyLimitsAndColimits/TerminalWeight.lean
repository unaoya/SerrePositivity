module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.WeightedFunctor
public import Mathlib.CategoryTheory.HomCongr

/-!
概要：終対象である重みについて、重み付き end と strict 極限を同定する。
方針：重みの変数を忘れる射が同型になることを示し、Hom の普遍性で比較射を検出する。
規約：比較射は既存の weightedConeComparison そのもの。Kan 性は不要。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、離散図式の homotopy 積の計算。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I]

/-- 概要：各成分が終対象である図式は図式の圏でも終対象。
方針：成分の一意な射を自然変換にまとめ、自然性と一意性を終対象性で示す。
規約：添字圏は任意の小圏。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、Bousfield–Kan の離散添字の重み。 -/
def weightIsTerminalOfObj (W : I ⥤ SSet.{u}) (hW : ∀ i, IsTerminal (W.obj i)) :
    IsTerminal W :=
  IsTerminal.ofUniqueHom
    (fun H ↦
      { app := fun i ↦ (hW i).from (H.obj i)
        naturality := fun _ j _ ↦ (hW j).hom_ext _ _ })
    (fun _ _ ↦ NatTrans.ext (funext fun i ↦ (hW i).hom_ext _ _))

/-- 概要：終対象の重みの変数を忘れる自然変換は同型。
方針：終対象への一意な射と恒等射の組を逆射にする。
規約：重みの終対象性は図式の圏で仮定する。
使われ方：Kerodon 7.5.4.1（Tag 03B6） の積における標準比較の計算。 -/
lemma weightedParameterProjection_isIso (W : I ⥤ SSet.{u}) (hW : IsTerminal W)
    (A : SSet.{u}) : IsIso (snd W ((Functor.const I).obj A)) := by
  refine ⟨⟨lift (hW.from ((Functor.const I).obj A)) (𝟙 _), ?_, ?_⟩⟩
  · apply CartesianMonoidalCategory.hom_ext
    · exact hW.hom_ext _ _
    · simp
  · exact lift_snd _ _

/-- 概要：終対象の重みでは strict 極限の標準比較射が同型。
方針：極限の普遍性、重みを忘れる同型、end の普遍性を合成して Yoneda で検出する。
規約：単なる同型の存在ではなく weightedConeComparison の同型性を示す。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、有限積と空積の具体的な比較射。 -/
lemma weightedConeComparison_isIso_of_isTerminalWeight (W : I ⥤ SSet.{u})
    (hW : IsTerminal W) {H : I ⥤ SSet.{u}} (c : Cone H) (hc : IsLimit c) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W c) := by
  apply isIso_of_yoneda_map_bijective
  intro A
  have := weightedParameterProjection_isIso W hW A
  let e : (A ⟶ c.pt) ≃ (A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSections W H) :=
    hc.homEquiv.trans
      (((asIso (snd W ((Functor.const I).obj A))).homCongr (Iso.refl H)).symm.trans
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsHomEquiv W H A).symm)
  have he (f : A ⟶ c.pt) : e f = f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W c := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsLift
      (snd W ((Functor.const I).obj A) ≫ (c.extend f).π ≫ 𝟙 H) = _
    rw [Category.comp_id]
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison W (c.extend f) = _
    have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeComparison_naturality W (c.extend f) c f (𝟙 H)
      (fun i ↦ by simp)
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedSectionsMap_id, Category.comp_id] using h.symm
  simpa only [← he] using e.bijective

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
