module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeInitialHom

/-!
概要：coherent simplex の始点を全 Hom パラメータで取り替えた実際の simplex を構成する。
方針：初点からの合成則と元の tail の豊穣関手則を、八通りの頂点の配置で組み合わせる。
規約：tail の strict 性・局所 Kan 性・極限性を要求しない。
使われ方：HTT 4.2.4.1 の錐全体上の族を単体ごとに構成する入力。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- 初点を x に取り替え、元の tail を保つパラメータ付き coherent simplex。 -/
def coneInitialSimplex (x : C) {n : ℕ} (T : (SimplicialNerve C) _⦋n + 1⦌)
    (p : Δ[n] ⟶ (SimplicialCategory.sHom x (T.obj ⟨ULift.up 0⟩)).op) :
    (SimplicialNerve C) _⦋n + 1⦌ where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialObj x T i.as.down
  map i j := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialHom x T p i.as.down j.as.down
  map_id := by
    rintro ⟨⟨i⟩⟩
    induction i using Fin.cases with
    | zero =>
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      intro a
      rfl
    | succ i => exact T.map_id ⟨ULift.up i.succ⟩
  map_comp := by
    rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩ ⟨⟨k⟩⟩
    induction i using Fin.cases <;> induction j using Fin.cases <;>
      induction k using Fin.cases
    all_goals
      apply SSet.hom_ext
      intro d
      apply ConcreteCategory.hom_ext
      rintro ⟨P, Q⟩
    case zero.zero.zero =>
      change (eId SSet x).app d PUnit.unit =
        (eComp SSet x x x).app d
          ((eId SSet x).app d PUnit.unit, (eId SSet x).app d PUnit.unit)
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app x x d _).symm
    case zero.zero.succ k =>
      change (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialHead x T p k).app d
          ((eComp SSet
            (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
            ⟨ULift.up 0⟩ ⟨ULift.up k.succ⟩).app d (P, Q)) =
        (eComp SSet x x (T.obj ⟨ULift.up k.succ⟩)).app d
          ((eId SSet x).app d PUnit.unit, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialHead x T p k).app d Q)
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialHom_id_comp_app]
      congr 1
      apply CategoryTheory.Functor.ext (fun t ↦ ?_)
      have hp : P.obj t = 𝟙 (⟨ULift.up 0⟩ : SimplicialThickening
          (ULift.{u} (Fin (n + 2)))) := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.thickeningPath_end_eq_id _ _
      change P.obj t ≫ Q.obj t = Q.obj t
      rw [hp, Category.id_comp]
    case zero.succ.zero j =>
      have h := Path.le (Q.obj 0)
      change j.succ ≤ 0 at h
      simp at h
    case zero.succ.succ j k =>
      let L := SimplicialThickening (ULift.{u} (Fin (n + 2)))
      exact congrArg
        (fun f : SimplicialCategory.sHom (⟨ULift.up 0⟩ : L) ⟨ULift.up j.succ⟩ ⊗
            SimplicialCategory.sHom (⟨ULift.up j.succ⟩ : L) ⟨ULift.up k.succ⟩ ⟶
              SimplicialCategory.sHom x (T.obj ⟨ULift.up k.succ⟩) ↦ f.app d (P, Q))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialHead_comp x T p j k)
    case succ.zero.zero i =>
      have h := Path.le (P.obj 0)
      change i.succ ≤ 0 at h
      simp at h
    case succ.zero.succ i k =>
      have h := Path.le (P.obj 0)
      change i.succ ≤ 0 at h
      simp at h
    case succ.succ.zero i j =>
      have h := Path.le (Q.obj 0)
      change j.succ ≤ 0 at h
      simp at h
    case succ.succ.succ i j k =>
      let L := SimplicialThickening (ULift.{u} (Fin (n + 2)))
      exact congrArg
        (fun f : SimplicialCategory.sHom (⟨ULift.up i.succ⟩ : L) ⟨ULift.up j.succ⟩ ⊗
            SimplicialCategory.sHom (⟨ULift.up j.succ⟩ : L) ⟨ULift.up k.succ⟩ ⟶
              SimplicialCategory.sHom (T.obj ⟨ULift.up i.succ⟩)
                (T.obj ⟨ULift.up k.succ⟩) ↦ f.app d (P, Q))
        (T.map_comp ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ⟨ULift.up k.succ⟩)

/-- 取り替えた simplex の最初の頂点は指定した x。 -/
lemma coneInitialSimplex_apex (x : C) {n : ℕ} (T : (SimplicialNerve C) _⦋n + 1⦌)
    (p : Δ[n] ⟶ (SimplicialCategory.sHom x (T.obj ⟨ULift.up 0⟩)).op) :
    (SimplicialNerve C).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
      (coneInitialSimplex x T p) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) (fun i j ↦ ?_)
  change (_ ≫ toUnit _) ≫ eId SSet x ≫
    eqToHom (rfl : SimplicialCategory.sHom x x = _) = toUnit _ ≫ eId SSet x
  simp only [comp_toUnit, eqToHom_refl, Category.comp_id]

/-- 最初の頂点を除いた面は元の coherent simplex の同じ面そのもの。 -/
lemma coneInitialSimplex_tail (x : C) {n : ℕ} (T : (SimplicialNerve C) _⦋n + 1⦌)
    (p : Δ[n] ⟶ (SimplicialCategory.sHom x (T.obj ⟨ULift.up 0⟩)).op) :
    (SimplicialNerve C).δ 0 (coneInitialSimplex x T p) = (SimplicialNerve C).δ 0 T := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) (fun i j ↦ ?_)
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
