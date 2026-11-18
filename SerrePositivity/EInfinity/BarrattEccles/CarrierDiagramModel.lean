module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.EvaluationFamily

public import SerrePositivity.EInfinity.BarrattEccles.CarrierDiagramSmallness
public import SerrePositivity.HomotopicalAlgebra.Transfer.CellMap
public import Mathlib.CategoryTheory.SmallObject.TransfiniteCompositionLifting

/-!
# 任意の小圏上の複体図式の具体的な射影モデル

概要：Hovey §2.1・§2.3 の複体図式の射影モデルを具体的に構成する。
方針：評価随伴と実際の複体の生成族を使う。
規約：任意の小圏・可換環、局所表示可能性の追加仮定なし。
使われ方：底の定値図式からの局所化 Hom と一般右導来極限。
-/

@[expose] public section

noncomputable section

universe u v

namespace SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram

open CategoryTheory Limits HomotopicalAlgebra
open scoped ZeroObject
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A] (K : Type u) [SmallCategory K]

local instance : HasColimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩

/-- 概要：複体図式の J-cell は頂点ごとに擬同型（Hovey §2.1・§2.3）。
方針：評価の余極限保存と trivial cofibration の閉性を使う。
規約：セルの始域に cofibrancy を追加しない。
使われ方：評価族への完全なモデル転送。 -/
lemma freeCells_acyclic :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    SerrePositivity.Quillen.relativeCells.{u}
      (generators A K (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A)) ≤
      ModelGeneration.EvaluationFamily.detected (evaluation A K)
        (weakEquivalences (Complex A)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory_cofibrantlyGenerated A
  have hgen (l : K) : generators A K (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A) ≤
      (trivialCofibrations (Complex A)).inverseImage (evaluation A K l) := by
    intro X Y f hf
    change (⨆ k, (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A).strictMap (free A K k)) f at hf
    rw [MorphismProperty.iSup_iff] at hf
    obtain ⟨k, hf⟩ := hf
    cases hf with
    | @map X Y f hf =>
      have ht : trivialCofibrations (Complex A) f :=
        ((_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A).le_llp_rlp.trans
          (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.trivialCofibrations_eq_generated (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A)
            (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A)).symm.le) _ hf
      have : Cofibration f := ⟨ht.1⟩
      have : WeakEquivalence f := ⟨ht.2⟩
      exact mem_trivialCofibrations (Limits.Sigma.map (fun _ : k ⟶ l => f))
  dsimp only
  intro X Y f hf l
  have hc : SerrePositivity.Quillen.relativeCells.{u} (trivialCofibrations (Complex A)) ≤
      trivialCofibrations (Complex A) := by
    rw [← fibrations_llp]
    exact (MorphismProperty.transfiniteCompositions_monotone
      ((MorphismProperty.pushouts_monotone (fibrations (Complex A)).llp.coproducts_le).trans
        (fibrations (Complex A)).llp.pushouts_le)).trans
          (fibrations (Complex A)).llp.transfiniteCompositions_le
  have h := ModelGeneration.relativeCells_map_le (evaluation A K l) _
    (trivialCofibrations (Complex A)) (hgen l) f hf
  exact (hc _ h).2
/-- 概要：任意の小圏上の複体図式の完全な射影モデル（Hovey §2.1・§2.3）。
方針：評価族の随伴・小対象性・非循環性を転送へ渡す。
規約：任意の可換環でモデル構造を局所的に選ぶ。
使われ方：底の定値図式からの導来 Hom。 -/
@[instance_reducible]
def projectiveModelCategory : ModelCategory (K ⥤ Complex A) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory_cofibrantlyGenerated A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCategory (free A K) (evaluation A K)
    (adjunction A K) (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A)
      (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A) (freeCells_acyclic A K)
/-- 概要：図式の弱同値は頂点ごとの擬同型（Hovey §2.1・§2.3）。
方針：元の評価族の検出するクラスを展開する。
規約：具体的な図式モデルを使う。
使われ方：底の図式の局所化との照合。 -/
lemma weakEquivalence_iff {F G : K ⥤ Complex A} (f : F ⟶ G) :
    let := projectiveModelCategory A K
    WeakEquivalence f ↔ ∀ k, QuasiIso (f.app k) := by
  let := projectiveModelCategory A K
  change WeakEquivalence f ↔ _
  rw [HomotopicalAlgebra.weakEquivalence_iff]
  rfl
/-- 概要：複体図式の fibration は全頂点・全次数で全射（Hovey §2.1・§2.3）。
方針：具体的な評価族の右類を展開する。
規約：添字と整数次数の全称条件。
使われ方：図式 frame と置換の条件。 -/
lemma fibration_iff {F G : K ⥤ Complex A} (f : F ⟶ G) :
    let := projectiveModelCategory A K
    Fibration f ↔ ∀ k, ∀ n : ℤ, Function.Surjective ((f.app k).f n) := by
  let := projectiveModelCategory A K
  change Fibration f ↔ _
  rw [HomotopicalAlgebra.fibration_iff]
  rfl
/-- 概要：複体図式モデルは元の I・J の自由像で生成される（Hovey §2.1・§2.3）。
方針：評価族の生成類判定へ同じ非循環性を渡す。
規約：分解の存在は証明済みの小対象性から供給する。
使われ方：図式の関手的置換と写像空間。 -/
lemma cofibrantlyGenerated :
    let := projectiveModelCategory A K
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{u}
      (generators A K (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A))
      (generators A K (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A)) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory_cofibrantlyGenerated A
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.modelCategory_generated (free A K) (evaluation A K)
    (adjunction A K) (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingCofibrations A)
      (_root_.SerrePositivity.ProjectiveModel.projectiveGeneratingTrivialCofibrations A) (freeCells_acyclic A K)
/-- 概要：すべての複体図式は具体的な射影モデルで fibrant（Hovey §2.1・§2.3）。
方針：零図式への射の各成分の全射性を示す。
規約：通常極限の右 Quillen 性は主張しない。
使われ方：図式の局所化 Hom の frame 計算。 -/
lemma isFibrant (F : K ⥤ Complex A) :
    let := projectiveModelCategory A K
    letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩
    IsFibrant F := by
  let := projectiveModelCategory A K
  letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩
  change IsFibrant F
  apply (isFibrant_iff_of_isTerminal (0 : F ⟶ (0 : K ⥤ Complex A))
    (isZero_zero _).isTerminal).mpr
  apply (fibration_iff A K _).mpr
  intro k n y
  have hz : IsZero (((0 : K ⥤ Complex A).obj k).X n) :=
    ((evaluation A K k) ⋙ HomologicalComplex.eval (ModuleCat A) (.up ℤ) n).map_isZero
      (isZero_zero (K ⥤ Complex A))
  have := ModuleCat.subsingleton_of_isZero hz
  exact ⟨0, Subsingleton.elim _ _⟩

/-- 概要：すべての非有界複体は具体的な射影モデルで fibrant（Hovey §2.3）。
方針：零複体への射の各次数の全射性を使う。
規約：モデル構造は局所的に選び、大域 instance にしない。
使われ方：各値の frame Hom の Kan 性。 -/
lemma complex_isFibrant (X : Complex A) :
    let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
    letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩
    IsFibrant X := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  letI : HasLimitsOfSize.{u, u} (Complex A) := ⟨fun _ _ => inferInstance⟩
  change IsFibrant X
  apply (isFibrant_iff_of_isTerminal (0 : X ⟶ (0 : Complex A))
    (isZero_zero _).isTerminal).mpr
  apply (HomotopicalAlgebra.fibration_iff _).mpr
  intro n y
  have hz : IsZero ((0 : Complex A).X n) :=
    (HomologicalComplex.eval (ModuleCat A) (.up ℤ) n).map_isZero (isZero_zero (Complex A))
  have := ModuleCat.subsingleton_of_isZero hz
  exact ⟨0, Subsingleton.elim _ _⟩

end SerrePositivity.EInfinity.BarrattEccles.CarrierDiagram
