module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedAssignedHom
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TriangleSeparatedMiddleEnriched

/-!
概要：二短辺の元の全単体と、分離座標の長 Hom から、全次数で実際の coherent 単体を作る。
方針：中間対象の三ラベルで合成則を分け、二つの単位側と元の内部合成を照合する。
規約：K・L は任意。Kan 性は延長 M の構成で使い、この組立てでは要求しない。
使われ方：Ind-S (9) の全族 encoder の単体データ。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {X Y Z : C}
  {K L : SSet.{max u v}}
  (f : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Y))
  (g : K ⟶ (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom Y Z))
  (M : (Δ[1] : SSet.{max u v}) ⊗ ((K ⊗ K) ⊗ L) ⟶
    (SSet.uliftFunctor.{v, u}).obj (SimplicialCategory.sHom X Z))
  (hM : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 ((K ⊗ K) ⊗ L) ≫ M =
    CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst (K ⊗ K) L ≫ CartesianMonoidalCategory.fst K K ≫ f)
      (CartesianMonoidalCategory.fst (K ⊗ K) L ≫ CartesianMonoidalCategory.snd K K ≫ g) ≫
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftTensorIso.{u, v}
      (SimplicialCategory.sHom X Y) (SimplicialCategory.sHom Y Z)).inv ≫
      (SSet.uliftFunctor.{v, u}).map (eComp SSet X Y Z))

include hM in
/-- 置換対象の全 Hom の合成則。 -/
lemma triangleSeparatedReplacementHom_comp {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌)
    (t : Fin (n + 1) →o Fin 3) (i j k : Fin (n + 1))
    (_hij : i ≤ j) (_hjk : j ≤ k) (hi : t i = 0) (hk : t k = 2) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap (ULift.up i) (ULift.up j) (ULift.up k) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedReplacementHom f g M s r t i k hi hk =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom f g M s r t i j ⊗ₘ
        _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom f g M s r t j k) ≫
        eComp SSet ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline f g s t).obj ⟨ULift.up i⟩)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline f g s t).obj ⟨ULift.up j⟩)
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline f g s t).obj ⟨ULift.up k⟩) := by
  have cases : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  rcases cases (t j) with hj | hj | hj
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_zero f g s t i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_zero f g s t j hj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_two f g s t k hk) _ _ _ _).2
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedReplacementHom_normalized f g M s r t i k hi hk,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom_zero f g M s r t i j hi hj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom_long f g M s r t j k hj hk]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom_comp_zero M s r t hi hj]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app X Z d _).symm
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_zero f g s t i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_one f g s t j hj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_two f g s t k hk) _ _ _ _).2
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedReplacementHom_normalized f g M s r t i k hi hk,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom_first f g M s r t i j hi hj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom_last f g M s r t j k hj hk]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom_comp_middle_enriched f g M hM s r t hi hj
  · apply (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_map_comp_iff_normalized
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_zero f g s t i hi)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_two f g s t j hj)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline_obj_two f g s t k hk) _ _ _ _).2
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedReplacementHom_normalized f g M s r t i k hi hk,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom_long f g M s r t i j hi hj,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedAssignedHom_two f g M s r t j k hj hk]
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.pathCompMap]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedLongHom_comp_two M s r t hi hj]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_comp_id_app X Z d _).symm

/-- 二短辺を保ち、分離した全パラメーターの長 Hom を持つ実際の coherent 単体。 -/
def triangleSeparatedSimplex {n : ℕ} (s : K _⦋n⦌) (r : L _⦋n⦌)
    (t : Fin (n + 1) →o Fin 3) : (SimplicialNerve C) _⦋n⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleLabelReplaceLongHoms (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedBaseline f g s t) t
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleSeparatedReplacementHom f g M s r t)
    (triangleSeparatedReplacementHom_comp f g M hM s r t)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
