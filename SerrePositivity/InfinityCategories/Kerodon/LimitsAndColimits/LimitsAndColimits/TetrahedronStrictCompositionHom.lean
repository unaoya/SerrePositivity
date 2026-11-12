module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.StrictFaceHomConstancy
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomMono
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TetrahedronFoldedLongHom

/-!
概要：二つの厳密合成面から、長い Hom の二内部合成面の共通定値性を導く。
方針：各真部分 Hom の定値性と豊穣合成則を使い、最大 path で二つの定値を照合する。
規約：元の三単体の全 native Hom を使う。
使われ方：Ind-S (9b) の畳み込みに必要な条件の放電。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits


/-- 二つの定値 Hom を合成すると、元の豊穣合成の頂点に定値。 -/
lemma tensor_const_post {A B X Y Z : SSet.{u}} (x : X _⦋0⦌) (y : Y _⦋0⦌)
    (m : X ⊗ Y ⟶ Z) :
    ((SSet.const x : A ⟶ X) ⊗ₘ (SSet.const y : B ⟶ Y)) ≫ m =
      SSet.const (m.app (Opposite.op ⦋0⦌) (x, y)) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨a, b⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map m (x, y) n

/-- 全内部合成面が個別に定値なら、最大 path で評価した同じ値に定値。 -/
lemma tetrahedron_composites_common_constant {H : SSet.{u}}
    (m : nerve (Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3)) ⟶ H)
    (hc : ∀ j : Fin 4, 0 < j → j < 3 → ∃ c,
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 4)) (ULift.up j) (ULift.up 3) ≫ m = SSet.const c) :
    ∃ c, ∀ j : Fin 4, 0 < j → j < 3 →
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 4)) (ULift.up j) (ULift.up 3) ≫ m = SSet.const c := by
  let P : Path (ULift.up (0 : Fin 4) : ULift.{u} (Fin 4)) (ULift.up 3) :=
    { I := Set.univ
      left_le := fun _ _ => Fin.zero_le _
      le_right := fun _ _ => Fin.le_last _ }
  refine ⟨m.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ P), ?_⟩
  intro j hj₀ hj₃
  obtain ⟨c, hc⟩ := hc j hj₀ hj₃
  have hr : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up (0 : Fin 4)) (c := ULift.up 3) (ULift.up j)).ι ≫ m =
      SSet.const c := by
    apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso (ULift.up (0 : Fin 4)) (ULift.up j) (ULift.up 3)).hom).1
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThroughIso_hom_ι, SSet.comp_const]
    exact hc
  let p : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathThrough (a := ULift.up (0 : Fin 4)) (c := ULift.up 3) (ULift.up j) : SSet) _⦋0⦌ :=
    ⟨ComposableArrows.mk₀ P, fun _ => Set.mem_univ _⟩
  have he := congrArg (fun F => F.app (Opposite.op ⦋0⦌) p) hr
  change m.app (Opposite.op ⦋0⦌) (ComposableArrows.mk₀ P) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant c 0 at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] at he
  rw [hc, he]

/-- 四つの真部分 Hom の定値性から、二つの内部合成面の同じ定値性を回収する。 -/
lemma tetrahedron_composites_exists_const
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (t : (SimplicialNerve C) _⦋3⦌)
    (h₀₁ : ∃ c, t.map ⟨ULift.up 0⟩ ⟨ULift.up 1⟩ = SSet.const c)
    (h₁₃ : ∃ c, t.map ⟨ULift.up 1⟩ ⟨ULift.up 3⟩ = SSet.const c)
    (h₀₂ : ∃ c, t.map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩ = SSet.const c)
    (h₂₃ : ∃ c, t.map ⟨ULift.up 2⟩ ⟨ULift.up 3⟩ = SSet.const c) :
    ∃ c, ∀ j : Fin 4, 0 < j → j < 3 →
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 4)) (ULift.up j) (ULift.up 3) ≫
        t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩ = SSet.const c := by
  apply tetrahedron_composites_common_constant
  intro j hj₀ hj₃
  have hj : j = 1 ∨ j = 2 := by omega
  rcases hj with rfl | rfl
  · obtain ⟨c₀₁, hc₀₁⟩ := h₀₁
    obtain ⟨c₁₃, hc₁₃⟩ := h₁₃
    erw [t.map_comp, hc₀₁, hc₁₃, tensor_const_post]
    exact ⟨_, rfl⟩
  · obtain ⟨c₀₂, hc₀₂⟩ := h₀₂
    obtain ⟨c₂₃, hc₂₃⟩ := h₂₃
    erw [t.map_comp, hc₀₂, hc₂₃, tensor_const_post]
    exact ⟨_, rfl⟩

/-- 零番面と三番面が厳密な順序図式なら、畳み込みの合成条件を満たす。 -/
lemma tetrahedron_strict_faces_composites
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (t : (SimplicialNerve C) _⦋3⦌)
    (A B : ULift.{u} (Fin 3) ⥤ C)
    (h₀ : (SimplicialNerve C).δ (0 : Fin 4) t = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram A)
    (h₃ : (SimplicialNerve C).δ (3 : Fin 4) t = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram B) :
    ∃ c, ∀ j : Fin 4, 0 < j → j < 3 →
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up (0 : Fin 4)) (ULift.up j) (ULift.up 3) ≫
        t.map ⟨ULift.up 0⟩ ⟨ULift.up 3⟩ = SSet.const c := by
  apply tetrahedron_composites_exists_const t
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexHom_exists_const_of_strict_face t 3 B h₃ 0 1 (by decide) (Or.inr (by decide))
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexHom_exists_const_of_strict_face t 0 A h₀ 0 2 (by decide) (Or.inl (by decide))
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexHom_exists_const_of_strict_face t 3 B h₃ 0 2 (by decide) (Or.inr (by decide))
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.simplexHom_exists_const_of_strict_face t 0 A h₀ 1 2 (by decide) (Or.inl (by decide))

/-- 指定三面を保ち、欠面の全 native Hom を一番面と一致させる実三単体。 -/
lemma tetrahedron_normalize_of_strict_faces
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (t : (SimplicialNerve C) _⦋3⦌)
    (A B : ULift.{u} (Fin 3) ⥤ C)
    (h₀ : (SimplicialNerve C).δ (0 : Fin 4) t = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram A)
    (h₃ : (SimplicialNerve C).δ (3 : Fin 4) t = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram B) :
    ∃ t' : (SimplicialNerve C) _⦋3⦌,
      (SimplicialNerve C).δ (0 : Fin 4) t' = (SimplicialNerve C).δ (0 : Fin 4) t ∧
      (SimplicialNerve C).δ (1 : Fin 4) t' = (SimplicialNerve C).δ (1 : Fin 4) t ∧
      (SimplicialNerve C).δ (3 : Fin 4) t' = (SimplicialNerve C).δ (3 : Fin 4) t ∧
      HEq (((SimplicialNerve C).δ (2 : Fin 4) t').map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩)
        (((SimplicialNerve C).δ (1 : Fin 4) t).map ⟨ULift.up 0⟩ ⟨ULift.up 2⟩) := by
  obtain ⟨c, hc⟩ := tetrahedron_strict_faces_composites t A B h₀ h₃
  let t' := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronWithFoldedLongHom t c hc
  have h₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronWithFoldedLongHom_face_one t c hc
  have hh := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedron_nativeLongHom_eq_of_fold t'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronWithFoldedLongHom_invariant t c hc)
  exact ⟨t', _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronWithFoldedLongHom_face_zero t c hc, h₁,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.tetrahedronWithFoldedLongHom_face_three t c hc,
    (heq_of_eq hh.symm).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctor_map_heq h₁ _ _)⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
