module
public import SerrePositivity.KST.ProExcision.GroupHomotopyFunctoriality

/-!
# 実線形区間の自然な正方形の加減法

概要：区間射の自然な正方形は加減法と定数区間の構成で保たれる。
方針：合成の加法性と区間射影の自然性を使う。
規約：KST A.5・A.6・4.16、非被約模型の augmentation 補正。
使われ方：実帰納ホモトピーの線形な連結と相殺の係数自然性。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
variable {A A' B B' : SimplicialObject (ModuleCat.{u} ℤ)}

/-- 概要：自然な二つの区間射の和も自然。
方針：合成を和に分配する。
規約：KST 4.16。使われ方：帰納比較の線形な連結。 -/
lemma cylinderSquare_add {a : A ⟶ A'} {b : B ⟶ B'} {h k : A ⟶ B} {h' k' : A' ⟶ B'}
    (hh : a ≫ h' = h ≫ b) (hk : a ≫ k' = k ≫ b) : a ≫ (h' + k') = (h + k) ≫ b := by
  simp only [Preadditive.comp_add, Preadditive.add_comp, hh, hk]

/-- 概要：自然な二つの区間射の差も自然。
方針：合成を差に分配する。
規約：KST 4.16 の augmentation 補正の相殺。
使われ方：実帰納比較の補正と相殺。 -/
lemma cylinderSquare_sub {a : A ⟶ A'} {b : B ⟶ B'} {h k : A ⟶ B} {h' k' : A' ⟶ B'}
    (hh : a ≫ h' = h ≫ b) (hk : a ≫ k' = k ≫ b) : a ≫ (h' - k') = (h - k) ≫ b := by
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, hh, hk]

/-- 概要：自然な射の定数区間は自然。
方針：区間射影の自然性と元の射の正方形を合成する。
規約：KST A.3・4.16。使われ方：連結時の中間定数射と相殺の定数射。 -/
lemma cylinderSquare_constant {X X' : SSet.{u}} {D D' : SimplicialObject (ModuleCat.{u} ℤ)}
    (x : X ⟶ X') (b : D ⟶ D') (f : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X ⟶ D) (f' : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace X' ⟶ D')
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpaceMap x ≫ f' = f ≫ b) :
    linearizedCylinderMap x ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderProjection X' ≫ f') =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderProjection X ≫ f) ≫ b := by
  rw [← Category.assoc, linearizedCylinderProjection_naturality, Category.assoc, hf, Category.assoc]

end SerrePositivity.KST.ProExcision
