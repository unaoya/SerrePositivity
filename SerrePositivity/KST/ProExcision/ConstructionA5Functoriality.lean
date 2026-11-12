module
public import SerrePositivity.KST.ProExcision.TensorAugmentationFunctoriality
public import SerrePositivity.KST.ProExcision.ConstructionA5
public import SerrePositivity.KST.ProExcision.GroupHomotopyOperations
public import SerrePositivity.KST.ProExcision.LinearizedGroupProductNaturality

/-!
# μ 版 A.5 の異なる群データ間の関手性

概要：因子内の入力ホモトピーを結ぶ可換な正方形から、構成した A.5 の実区間射の自然性を導く。
方針：群準同型の自由化の合成則、対角・μ の自然性、一般テンソル比較の関手性を合成する。
規約：KST A.5 の augmentation 補正と Lemma 4.16 の (I,a) の射への関手性。
使われ方：非可換な係数環の変更と単体環の各次数間の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory

/-- 概要：群準同型の可換な正方形は自由化の可換な正方形を与える。
方針：自由化の合成則と準同型の外延性を使う。
規約：KST App. A。使われ方：A.5 の因子の入力射の自然性。 -/
lemma groupLinearizedMap_square {T P T' P' : Type u} [Group T] [Group P] [Group T'] [Group P']
    (α : T →* P) (α' : T' →* P') (t : T →* T') (p : P →* P')
    (h : ∀ x, α' (t x) = p (α x)) :
    groupLinearizedMap t ≫ groupLinearizedMap α' = groupLinearizedMap α ≫ groupLinearizedMap p := by
  rw [groupLinearizedMap_comp, groupLinearizedMap_comp]
  apply congrArg groupLinearizedMap
  apply MonoidHom.ext
  exact h

/-- 概要：μ 版 A.5 の実区間射は異なる群データ間の写像に自然。
方針：因子内の自然性と対角・μ の可換性を一般テンソルの実比較へ渡す。
規約：KST A.5 の augmentation 補正、非可換な標的と明示的な因子のホモトピー。
使われ方：Lemma 4.16 の環と指定元の対に関する関手性。 -/
lemma constructionA5_functorial
    {T P Q H T₁ P₁ Q₁ H₁ : Type u}
    [Group T] [Group P] [Group Q] [Group H] [Group T₁] [Group P₁] [Group Q₁] [Group H₁]
    (d : GroupProductData T P Q H) (d₁ : GroupProductData T₁ P₁ Q₁ H₁) (m m' : ℕ)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap d.α) (groupLinearizedMap (1 : T →* P)) m)
    (k : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap d.β) (groupLinearizedMap (1 : T →* Q)) m')
    (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap d₁.α) (groupLinearizedMap (1 : T₁ →* P₁)) m)
    (k₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearizedMHomotopy (groupLinearizedMap d₁.β) (groupLinearizedMap (1 : T₁ →* Q₁)) m')
    (t : T →* T₁) (p : P →* P₁) (q : Q →* Q₁) (r : H →* H₁)
    (hα : ∀ x, d₁.α (t x) = p (d.α x)) (hβ : ∀ x, d₁.β (t x) = q (d.β x))
    (hμ : ∀ x y, d₁.μ (p x, q y) = r (d.μ (x, y)))
    (hh : linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ t)) ≫ h₁.h = h.h ≫ groupLinearizedMap p)
    (hk : linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ t)) ≫ k₁.h = k.h ≫ groupLinearizedMap q) :
    linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ t)) ≫ (constructionA5 d₁ m m' h₁ k₁).h =
      (constructionA5 d m m' h k).h ≫ groupLinearizedMap r := by
  exact linearizedTensorAugmentationMHomotopy_functorial h k h₁ k₁
    (linearizedDiagonal (nerve (SingleObj T))) (linearizedGroupProduct d.μ)
    (linearizedDiagonal (nerve (SingleObj T₁))) (linearizedGroupProduct d₁.μ)
    (nerveMap (SingleObj.mapHom _ _ t)) (nerveMap (SingleObj.mapHom _ _ t))
    (nerveMap (SingleObj.mapHom _ _ t)) (nerveMap (SingleObj.mapHom _ _ p))
    (nerveMap (SingleObj.mapHom _ _ q)) (nerveMap (SingleObj.mapHom _ _ r))
    (groupLinearizedMap_square d.α d₁.α t p hα) (groupLinearizedMap_square d.β d₁.β t q hβ)
    (groupLinearizedMap_square 1 1 t p (by intro x; simp only [MonoidHom.one_apply, map_one]))
    (groupLinearizedMap_square 1 1 t q (by intro x; simp only [MonoidHom.one_apply, map_one])) hh hk
    (linearizedDiagonal_naturality (nerveMap (SingleObj.mapHom _ _ t)))
    (linearizedGroupProduct_naturality d.μ d₁.μ p q r hμ)

end SerrePositivity.KST.ProExcision
