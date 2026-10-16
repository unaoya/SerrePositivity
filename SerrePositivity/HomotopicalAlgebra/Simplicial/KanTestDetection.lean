module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.AnodyneKanReplacement
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanHomotopyClasses

/-! # Model-free detection of anodyne localization by all Kan-valued homotopy tests

The proof uses only the actual horn replacement and its anodyne unit.
It applies in any value universe without installing a model structure.
-/

@[expose] public section
universe v uH vH
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.SimplicialModel.KanTestDetection
open HomotopyClasses
variable {X Y : SSet.{v}} (f : X ⟶ Y)

abbrev Tests : Prop := ∀ (K : SSet.{v}),
  SSet.modelCategoryQuillen.J.rlp (terminal.from K) → Function.Bijective (pre f (K := K))

lemma replacement_pre_square (K : SSet.{v}) :
    pre (AnodyneKanReplacement.unit.app X) (K := K) ∘
      pre (AnodyneKanReplacement.functor.map f) =
        pre f ∘ pre (AnodyneKanReplacement.unit.app Y) := by
  funext t
  refine Quot.inductionOn t (fun g => ?_)
  change mk (AnodyneKanReplacement.unit.app X ≫
      (AnodyneKanReplacement.functor.map f ≫ g)) =
    mk (f ≫ (AnodyneKanReplacement.unit.app Y ≫ g))
  have h : AnodyneKanReplacement.unit.app X ≫ AnodyneKanReplacement.functor.map f =
      f ≫ AnodyneKanReplacement.unit.app Y := (AnodyneKanReplacement.unit.naturality f).symm
  rw [← Category.assoc, h, Category.assoc]

lemma replacement_tests (hf : Tests f) : Tests (AnodyneKanReplacement.functor.map f) := by
  intro K hK
  have hX := KanHomotopyClasses.pre_bijective (AnodyneKanReplacement.unit.app X)
    (AnodyneKanReplacement.unit_anodyne X) hK
  have hY := KanHomotopyClasses.pre_bijective (AnodyneKanReplacement.unit.app Y)
    (AnodyneKanReplacement.unit_anodyne Y) hK
  apply (Function.Bijective.of_comp_iff' hX _).mp
  rw [replacement_pre_square]
  exact (hf K hK).comp hY

variable {H : Type uH} [Category.{vH} H] (L : SSet.{v} ⥤ H)
  (hL : SSet.anodyneExtensions.IsInvertedBy L)

include hL in
lemma map_isIso_of_tests (hf : Tests f) : IsIso (L.map f) := by
  have hr := replacement_tests f hf
  have : IsIso (L.map (AnodyneKanReplacement.functor.map f)) :=
    HomotopyClasses.map_isIso_of_tests L hL _
      (hr _ (AnodyneKanReplacement.terminal_rlp X)).surjective
      (hr _ (AnodyneKanReplacement.terminal_rlp Y)).injective
  have : IsIso (L.map (AnodyneKanReplacement.unit.app X)) :=
    hL _ (AnodyneKanReplacement.unit_anodyne X)
  have : IsIso (L.map (AnodyneKanReplacement.unit.app Y)) :=
    hL _ (AnodyneKanReplacement.unit_anodyne Y)
  have h := congrArg L.map (AnodyneKanReplacement.unit.naturality f)
  rw [L.map_comp, L.map_comp] at h
  have : IsIso (L.map f ≫ L.map (AnodyneKanReplacement.unit.app Y)) := h.symm ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp this

lemma tests_of_anodyneQ_isIso (hf : IsIso (AnodyneHomotopy.anodyneQ.map f)) : Tests f := by
  intro K hK
  have h := AnodyneHomotopy.map_isIso_of_anodyneQ_isIso
    (HomotopyClasses.functor K).rightOp (KanHomotopyClasses.rightOp_inverts K hK) f hf
  have : IsIso ((HomotopyClasses.functor K).map f.op) := (isIso_op_iff _).mp h
  exact (isIso_iff_bijective _).mp this

lemma anodyneQ_isIso_iff_tests : IsIso (AnodyneHomotopy.anodyneQ.map f) ↔ Tests f :=
  ⟨tests_of_anodyneQ_isIso f, map_isIso_of_tests f AnodyneHomotopy.anodyneQ
    (Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions)⟩

end SerrePositivity.SimplicialModel.KanTestDetection
