module
public import SerrePositivity.KST.ProExcision.StrictificationFunctoriality
public import SerrePositivity.KST.ProExcision.GroupHomotopyOperations
public import SerrePositivity.KST.ProExcision.ConstructionA5Functoriality

/-!
# 零次入力と共役比較の異なる群間の自然性

概要：A.5 の零次入力と A.6 の前合成した実比較は可換な群準同型の正方形に自然。
方針：線形区間の射影、テンソルの合成則、共役の標準比較の自然性を使う。
規約：KST A.5・A.6・Lemma 4.16 の (I,a) への関手性。
使われ方：実帰納ホモトピーの係数変更の帰納法。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory
open scoped Simplicial

/-- 概要：任意の単体的整数加群射の可換な正方形を線形区間にテンソルしても可換。
方針：テンソル写像の二因子の合成則を使う。
規約：KST A.3。使われ方：共役比較の前合成の自然性。 -/
lemma simplicialIntegerTensorInterval_square
    {A A' B B' : SimplicialObject (ModuleCat.{u} ℤ)}
    (a : A ⟶ A') (b : B ⟶ B') (f : A ⟶ B) (f' : A' ⟶ B') (hf : a ≫ f' = f ≫ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap a (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap f' (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.simplicialIntegerTensorMap b (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) := by
  have h₁ := simplicialIntegerTensorMap_comp a (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) f'
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})))
  have h₂ := simplicialIntegerTensorMap_comp f (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u}))) b
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedSpace (Δ[1] : SSet.{u})))
  simp only [Category.id_comp] at h₁ h₂
  rw [← h₁, ← h₂, hf]

/-- 概要：群の0次入力の実区間射は可換な群準同型の正方形に自然。
方針：射影の自然性と自由化の正方形を合成する。
規約：KST A.5・4.16 の帰納基底。
使われ方：帰納ホモトピーの係数変更の零次。 -/
lemma groupZeroMHomotopy_functorial
    {T T' H H' : Type u} [Group T] [Group T'] [Group H] [Group H']
    (f : T →* H) (f' : T' →* H') (t : T →* T') (r : H →* H')
    (hf : ∀ x, f' (t x) = r (f x)) :
    linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ t)) ≫ (groupZeroMHomotopy f').h =
      (groupZeroMHomotopy f).h ≫ groupLinearizedMap r := by
  change linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ t)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderProjection _ ≫ groupLinearizedMap f') =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderProjection _ ≫ groupLinearizedMap f) ≫ groupLinearizedMap r
  rw [← Category.assoc, linearizedCylinderProjection_naturality, Category.assoc]
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderProjection (nerve (SingleObj T)) ≫
    (groupLinearizedMap t ≫ groupLinearizedMap f') =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.linearizedCylinderProjection (nerve (SingleObj T)) ≫ groupLinearizedMap f) ≫ groupLinearizedMap r
  rw [groupLinearizedMap_square f f' t r hf, Category.assoc]

/-- 概要：前合成した共役の実 m 次比較は異なる群データに自然。
方針：前合成の区間正方形と標準共役ホモトピーの自然性を連結する。
規約：KST A.6・4.16、係数の射が u を u′ に送ることだけを用いる。
使われ方：実帰納ホモトピーの共役部分の係数変更。 -/
lemma groupConjugationMHomotopy_functorial
    {T T' H H' : Type u} [Group T] [Group T'] [Group H] [Group H']
    (f : T →* H) (f' : T' →* H') (t : T →* T') (r : H →* H')
    (hf : ∀ x, f' (t x) = r (f x)) (u : H) (u' : H') (hu : r u = u') (m : ℕ) :
    linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ t)) ≫ (groupConjugationMHomotopy f' u' m).h =
      (groupConjugationMHomotopy f u m).h ≫ groupLinearizedMap r := by
  have hpre := simplicialIntegerTensorInterval_square (groupLinearizedMap t) (groupLinearizedMap r)
    (groupLinearizedMap f) (groupLinearizedMap f') (groupLinearizedMap_square f f' t r hf)
  change linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ t)) ≫
    linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ f')) =
      linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ f)) ≫
        linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ r)) at hpre
  have hconj := conjugationLinearizedHomotopy_naturality r u
  rw [hu] at hconj
  change (conjugationLinearizedHomotopy u).h ≫ groupLinearizedMap r =
    linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ r)) ≫ (conjugationLinearizedHomotopy u').h at hconj
  change linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ t)) ≫
      (linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ f')) ≫ (conjugationLinearizedHomotopy u').h) =
    (linearizedCylinderMap (nerveMap (SingleObj.mapHom _ _ f)) ≫ (conjugationLinearizedHomotopy u).h) ≫
      groupLinearizedMap r
  rw [← Category.assoc, hpre, Category.assoc, ← hconj, Category.assoc]

end SerrePositivity.KST.ProExcision
