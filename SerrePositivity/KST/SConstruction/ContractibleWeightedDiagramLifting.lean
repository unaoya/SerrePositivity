module
public import SerrePositivity.KST.SConstruction.ContractibleDiagramSelections

/-! # 可縮な係数図式の weighted nerve の相対延長
概要：成分が可縮 Kan なら、全ての底の境界を同じ底の上で充填できる。
方針：終対象係数の射影の同型性と係数写像の自明 fibration 性を使う。
規約：単射上で指定済みの部分図式を厳密に保持する。
使われ方：入力射列の既存の面を保つ coherent な選択とその比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories SerrePositivity.InfinityCategories.HomotopyLimits
open scoped Simplicial

/-- 一点係数の weighted nerve は元の底の nerve と同型。 -/
lemma selectionTerminalWeightedProjection_isIso (I : Type u) [SmallCategory I] :
    IsIso (weightedNerveProjection (selectionTerminalDiagram I)) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  constructor
  · rintro ⟨σ, ψ⟩ ⟨τ, θ⟩ h
    change σ = τ at h
    subst τ
    have he : ψ = θ := by
      apply NatTrans.ext
      funext i
      exact terminal.hom_ext _ _
    cases he
    rfl
  · intro σ
    refine ⟨⟨σ, ?_⟩, rfl⟩
    exact { app i := terminal.from _
            naturality _ _ _ := terminal.hom_ext _ _ }

/-- 可縮な全係数の weighted nerve の射影は任意の単射に対する持ち上げ性を持つ。 -/
lemma contractibleWeightedDiagramProjection_trivialKanFibration
    {I : Type u} [SmallCategory I] (F : I ⥤ SSet.{u})
    (hF : ∀ i, IsContractibleKan (F.obj i)) :
    TrivialKanFibration (weightedNerveProjection F) := by
  let t := selectionTerminalMap F
  let (i : I) : TrivialKanFibration (t.app i) :=
    (isContractibleKan_iff_trivialKanFibration (F.obj i)).mp (hF i)
  have hq : TrivialKanFibration (weightedNerveMap t) := inferInstance
  let : IsIso (weightedNerveProjection (selectionTerminalDiagram I)) :=
    selectionTerminalWeightedProjection_isIso I
  rw [← weightedNerveMap_projection t]
  exact ⟨trivialKanFibrations.comp_mem _ _ hq.mem (MorphismProperty.rlp_of_isIso _ _)⟩

/-- 任意の単射上の coherent な部分図式は、指定した底の図式の上へ厳密に延長できる。 -/
lemma contractibleWeightedDiagram_relative_lifting {I : Type u} [SmallCategory I]
    (F : I ⥤ SSet.{u}) (hF : ∀ i, IsContractibleKan (F.obj i))
    {A B : SSet.{u}} (j : A ⟶ B) [Mono j]
    (a : A ⟶ weightedNerve F) (b : B ⟶ nerve I)
    (h : a ≫ weightedNerveProjection F = j ≫ b) :
    ∃ s : B ⟶ weightedNerve F, j ≫ s = a ∧ s ≫ weightedNerveProjection F = b := by
  have hp := contractibleWeightedDiagramProjection_trivialKanFibration F hF
  have := hp.mem j inferInstance
  let sq : CommSq a j (weightedNerveProjection F) b := ⟨h⟩
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- 底の単射上で指定した coherent な選択は、底全体の切断へ延長できる。 -/
lemma contractibleWeightedDiagram_section_extension {I : Type u} [SmallCategory I]
    (F : I ⥤ SSet.{u}) (hF : ∀ i, IsContractibleKan (F.obj i))
    {A : SSet.{u}} (j : A ⟶ nerve I) [Mono j]
    (a : A ⟶ weightedNerve F) (h : a ≫ weightedNerveProjection F = j) :
    ∃ s : nerve I ⟶ weightedNerve F, j ≫ s = a ∧ s ≫ weightedNerveProjection F = 𝟙 _ := by
  exact contractibleWeightedDiagram_relative_lifting F hF j a (𝟙 _) (by simpa using h)

end SerrePositivity.KST.SConstruction
