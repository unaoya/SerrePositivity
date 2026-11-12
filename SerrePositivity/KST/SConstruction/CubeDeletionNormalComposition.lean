module
public import SerrePositivity.KST.SConstruction.SerreCubeDeletionNormal

/-! # 削除標準表示の元の合成を保つ正規化
概要：二つの削除標準表示の合成を、同じ入力・出力を持つ一つの削除標準表示へ移す。
方針：元の保持・削除の選択を合成し、右端削除の自然性で Serre 評価も照合する。
規約：中間対象も元の合成射も保持する。使われ方：ブロック削除で生じる入力削除の吸収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

/-- 二つの元の削除標準表示を合成して一つの標準表示へ移す。 -/
def cubeDeletionNormalComp : {n a b : ℕ} → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n a →
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal a b → _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n b
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .drop d, e => .drop (cubeDeletionNormalComp d e)
  | _, _, _, .keep d, .drop e => .drop (cubeDeletionNormalComp d e)
  | _, _, _, .keep d, .keep e => .keep (cubeDeletionNormalComp d e)
termination_by structural _n _a _b d _e => d

/-- 削除標準表示の合成は、元の選択添字の合成を回収する。 -/
lemma cubeDeletionNormalComp_embedding {n a b : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n a)
    (e : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal a b) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding (cubeDeletionNormalComp d e) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding d ∘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding e := by
  induction d generalizing b with
  | nil => cases e; rfl
  | drop d ih =>
    funext i
    exact congrArg Fin.succ (congrFun (ih e) i)
  | keep d ih =>
    cases e with
    | drop e =>
      funext i
      simpa [cubeDeletionNormalComp, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding] using
        congrArg Fin.succ (congrFun (ih e) i)
    | keep e =>
      funext i
      refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · simpa [cubeDeletionNormalComp, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalEmbedding] using
          congrArg Fin.succ (congrFun (ih e) i)

/-- 削除標準表示の合成は、元の頂点関数の合成を厳密に回収する。 -/
lemma cubeDeletionNormalComp_vertex {n a b : ℕ} (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n a)
    (e : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal a b) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex (cubeDeletionNormalComp d e) =
      _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex e ∘ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.cubeDeletionNormalVertex d := by
  funext x i
  exact congrArg x (congrFun (cubeDeletionNormalComp_embedding d e) i)

/-- 削除標準表示の合成は、元の Serre 射の合成を厳密に回収する。 -/
lemma serreCubeDeletionNormal_comp (A : Type u) [CommRing A] {n a b : ℕ}
    (d : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal n a) (e : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CubeDeletionNormal a b) :
    serreCubeDeletionNormal A (cubeDeletionNormalComp d e) =
      serreCubeDeletionNormal A d ≫ serreCubeDeletionNormal A e := by
  induction d generalizing b with
  | nil => cases e; exact (Category.id_comp _).symm
  | drop d ih =>
    change serreCubeDegeneracy A _ 0 ≫ serreCubeDeletionNormal A (cubeDeletionNormalComp d e) = _
    rw [ih e]
    exact (Category.assoc _ _ _).symm
  | @keep n a d ih =>
    cases e with
    | drop e =>
      change serreCubeDegeneracy A n 0 ≫ serreCubeDeletionNormal A (cubeDeletionNormalComp d e) = _
      rw [ih e]
      let g : serreCubeComonoid A (n + 1) ⟶ serreCubeComonoid A (a + 1) :=
        serreCubeDeletionNormal A d ⊗ₘ 𝟙 (serreIntervalComonoid A)
      have hn : g ≫ serreCubeDegeneracy A a 0 =
          serreCubeDegeneracy A n 0 ≫ serreCubeDeletionNormal A d :=
        serreCubeDegeneracy_zero_naturality A _
      change serreCubeDegeneracy A n 0 ≫
        (serreCubeDeletionNormal A d ≫ serreCubeDeletionNormal A e) =
          g ≫ (serreCubeDegeneracy A a 0 ≫ serreCubeDeletionNormal A e)
      rw [← Category.assoc, ← hn, Category.assoc]
    | keep e =>
      change (serreCubeDeletionNormal A (cubeDeletionNormalComp d e) ⊗ₘ
          𝟙 (serreIntervalComonoid A)) =
        (serreCubeDeletionNormal A d ⊗ₘ 𝟙 (serreIntervalComonoid A)) ≫
          (serreCubeDeletionNormal A e ⊗ₘ 𝟙 (serreIntervalComonoid A))
      rw [ih e]
      simp only [tensorHom_comp_tensorHom, Category.comp_id]

end SerrePositivity.KST.SConstruction
