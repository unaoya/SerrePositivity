module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyDiagram

/-!
概要：coherent な変換の prism と射の prism から、全パラメーターの自然性の四角形を作る。
方針：変換の時刻、射の時刻、射のパラメーター、変換のパラメーターを別々に保持する。
規約：四辺とパラメーター制限の等式は厳密で、自然性を仮定として追加しない。
使われ方：表現対象の恒等射で回収した変換と元の coherent 変換の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories

/-- 変換と射の二つの時刻を保った、パラメーター付きの自然性の四角形。 -/
def functorNaturalitySquare {X Y K T : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ (X ⊗ T) ⟶ Y) (h : (Δ[1] : SSet.{u}) ⊗ K ⟶ X) :
    (Δ[1] : SSet.{u}) ⊗ (Δ[1] ⊗ (K ⊗ T)) ⟶ Y :=
  let A := (Δ[1] : SSet.{u})
  let P := K ⊗ T
  let s := snd A (A ⊗ P)
  let p := s ≫ snd A P
  lift (fst A (A ⊗ P))
    (lift (lift (s ≫ fst A P) (p ≫ fst K T) ≫ h) (p ≫ snd K T)) ≫ H

/-- 変換の端で制限した辺は、元の端点関手を射の prism に作用させる辺。 -/
lemma functorNaturalitySquare_transformationFace {X Y K T : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ (X ⊗ T) ⟶ Y) (h : (Δ[1] : SSet.{u}) ⊗ K ⟶ X)
    (i : Fin 2) (F : X ⟶ Y) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (X ⊗ T) ≫ H = fst X T ≫ F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (Δ[1] ⊗ (K ⊗ T)) ≫ functorNaturalitySquare H h =
      lift (fst (Δ[1] : SSet.{u}) (K ⊗ T))
        (snd (Δ[1] : SSet.{u}) (K ⊗ T) ≫ fst K T) ≫ h ≫ F := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, k, t⟩
  exact congrArg (fun f ↦ f.app n (h.app n (s, k), t)) hi

/-- 射の端で制限した辺は、その端点での元の変換の評価。 -/
lemma functorNaturalitySquare_arrowFace {X Y K T : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ (X ⊗ T) ⟶ Y) (h : (Δ[1] : SSet.{u}) ⊗ K ⟶ X)
    (i : Fin 2) (x : X _⦋0⦌) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i K ≫ h = SSet.const x) :
    (Δ[1] ◁ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint i (K ⊗ T)) ≫ functorNaturalitySquare H h =
      lift (fst (Δ[1] : SSet.{u}) (K ⊗ T))
        (lift (SSet.const x) (snd (Δ[1] : SSet.{u}) (K ⊗ T) ≫ snd K T)) ≫ H := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨s, k, t⟩
  exact congrArg (fun y ↦ H.app n (s, y, t)) (congrArg (fun f ↦ f.app n k) hi)

/-- 自然性の四角形は射と変換の両パラメーターの制限を厳密に保つ。 -/
lemma functorNaturalitySquare_restrict {X Y K K' T T' : SSet.{u}}
    (H : (Δ[1] : SSet.{u}) ⊗ (X ⊗ T) ⟶ Y) (h : (Δ[1] : SSet.{u}) ⊗ K ⟶ X)
    (k : K' ⟶ K) (t : T' ⟶ T) :
    (Δ[1] ◁ (Δ[1] ◁ (k ⊗ₘ t))) ≫ functorNaturalitySquare H h =
      functorNaturalitySquare ((Δ[1] ◁ (X ◁ t)) ≫ H) ((Δ[1] ◁ k) ≫ h) := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨i, j, x, y⟩
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories
