module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeInitialHom

/-!
概要：元の coherent な tail と合成を保つ head の係数から、実際の cone の単体を組む。
方針：初点固定の Hom データと八分岐の合成則で豊穣関手を構成する。
規約：head の合成則をデータとして明示し、weighted 係数への適用では既証明の合成則を渡す。
使われ方：左区間の共同評価を tail とする weighted pointed prism の単体。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

noncomputable section
variable {C : Type v} [Category.{u} C] [SimplicialCategory C]

/-- coherent な tail の全 Hom と合成を保つ、初点からの係数の族。 -/
structure CoherentConeHead (x : C) {n : ℕ} (T : (SimplicialNerve C) _⦋n + 1⦌) where
  hom (j : Fin (n + 1)) :
    nerve (Path (ULift.up 0 : ULift.{u} (Fin (n + 2))) (ULift.up j.succ)) ⟶
      SimplicialCategory.sHom x (T.obj ⟨ULift.up j.succ⟩)
  comp (i j : Fin (n + 1)) :
    eComp SSet (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
      ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩ ≫ hom j =
      (hom i ⊗ₘ T.map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩) ≫
        eComp SSet x (T.obj ⟨ULift.up i.succ⟩) (T.obj ⟨ULift.up j.succ⟩)

/-- 指定した head の係数と元の tail による全頂点間の Hom の作用。 -/
def coherentConeHomOfHead (x : C) {n : ℕ} (T : (SimplicialNerve C) _⦋n + 1⦌)
    (H : CoherentConeHead x T) (i j : Fin (n + 2)) :
    SimplicialCategory.sHom
      (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) ⟨ULift.up j⟩ ⟶
        SimplicialCategory.sHom (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialObj x T i) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialObj x T j) := by
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => exact toUnit _ ≫ eId SSet x
    | succ j => exact H.hom j
  | succ i =>
    induction j using Fin.cases with
    | zero => exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.weightedConeEmptyMap i _
    | succ j => exact T.map ⟨ULift.up i.succ⟩ ⟨ULift.up j.succ⟩

/-- 初点を x に取り替え、元の tail を保つパラメータ付き coherent simplex。 -/
def coherentConeSimplexOfHead (x : C) {n : ℕ} (T : (SimplicialNerve C) _⦋n + 1⦌)
    (H : CoherentConeHead x T) :
    (SimplicialNerve C) _⦋n + 1⦌ where
  obj i := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coneInitialObj x T i.as.down
  map i j := coherentConeHomOfHead x T H i.as.down j.as.down
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
      change (H.hom k).app d
          ((eComp SSet
            (⟨ULift.up 0⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2))))
            ⟨ULift.up 0⟩ ⟨ULift.up k.succ⟩).app d (P, Q)) =
        (eComp SSet x x (T.obj ⟨ULift.up k.succ⟩)).app d
          ((eId SSet x).app d PUnit.unit, (H.hom k).app d Q)
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
        (H.comp j k)
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
lemma coherentConeSimplexOfHead_apex (x : C) {n : ℕ} (T : (SimplicialNerve C) _⦋n + 1⦌)
    (H : CoherentConeHead x T) :
    (SimplicialNerve C).map (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ 0).op
      (coherentConeSimplexOfHead x T H) = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex x := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) (fun i j ↦ ?_)
  change (_ ≫ toUnit _) ≫ eId SSet x ≫
    eqToHom (rfl : SimplicialCategory.sHom x x = _) = toUnit _ ≫ eId SSet x
  simp only [comp_toUnit, eqToHom_refl, Category.comp_id]

/-- 最初の頂点を除いた面は元の coherent simplex の同じ面そのもの。 -/
lemma coherentConeSimplexOfHead_tail (x : C) {n : ℕ} (T : (SimplicialNerve C) _⦋n + 1⦌)
    (H : CoherentConeHead x T) :
    (SimplicialNerve C).δ 0 (coherentConeSimplexOfHead x T H) = (SimplicialNerve C).δ 0 T := by
  refine EnrichedFunctor.ext SSet (fun _ ↦ rfl) (fun i j ↦ ?_)
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end
end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
