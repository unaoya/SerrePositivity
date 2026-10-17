module
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorSecondMiddleRestriction
public import SerrePositivity.DifferentialGraded.Derived.BimoduleMiddleComparison
public import SerrePositivity.DifferentialGraded.Tensor.AssociatorNaturality

/-! # 第二中間圏の制限後の指定増大と通常結合子の整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t s
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]
  (D : Type z) [DGCategory A D] [Small.{u} D]
  (E : Type t) [DGCategory A E] [Small.{u} E]
  (T : Type s) [DGCategory A T] (F : DGFunctor A D E)
  (P : BimoduleCategory A B C) (Q : BimoduleCategory A C E)
  (R : BimoduleCategory A E T) (S : BimoduleCategory A D T)
  (q : S ⟶ (BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R)

local notation "P₀" => BimoduleCategory.underlying A B C P
local notation "Q₀" => BimoduleCategory.underlying A C E Q
local notation "R₀" => BimoduleCategory.underlying A E T R
local notation "S₀" => BimoduleCategory.underlying A D T S
local notation "LQ" => Bimodule.leftRestriction A C E D F Q₀
local notation "LQc" => BimoduleCategory.of A C D LQ
local notation "PQ" => BimoduleCategory.of A B E (compose A B C E P₀ Q₀)
local notation "LPQ" => Functor.obj (BimoduleCategory.middleLeftRestrictionFunctor A B E D F) PQ
local notation "PLQ" => BimoduleCategory.of A B D (compose A B C D P₀ LQ)

private lemma paste_square {V : Type*} [Category* V] {a b c d e f g h : V}
    (α : a ⟶ b) (β : b ⟶ c) (γ : c ⟶ d) (δ : d ⟶ e)
    (p : a ⟶ f) (u : f ⟶ c) (v : f ⟶ g) (w : g ⟶ e) (x : a ⟶ h) (y : h ⟶ g)
    (hi : α ≫ β = p ≫ u) (hs : u ≫ γ ≫ δ = v ≫ w) (hn : p ≫ v = x ≫ y) :
    α ≫ β ≫ γ ≫ δ = x ≫ y ≫ w := by
  rw [← Category.assoc α β, hi, Category.assoc, hs, ← Category.assoc p v, hn, Category.assoc]

/-- 第二中間圏を制限した後の任意の指定増大による比較と、通常結合子の可換square。 -/
lemma associatorIso_secondMiddleRestriction_resolved :
    composeMap A B D T (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 S) ≫
      middleRestrictionResolvedMap A B E D T F PQ R S q ≫
      (associatorIso A B C E T P₀ Q₀ R₀).hom =
    (associatorIso A B C D T P₀ LQ S₀).hom ≫
      composeMap A B C T (𝟙 P) (middleRestrictionResolvedMap A C E D T F Q R S q) := by
  have hn := associatorIso_naturality A B C D T (𝟙 P) (𝟙 LQc) q
  simp only [composeMap_id] at hn
  have hs := associatorIso_secondMiddleRestriction A B C D E T F P Q R
  have h₁ := composeMap_comp A B D T
    (composeLeftRestrictionIso A B C E D F P Q).hom (𝟙 LPQ) (𝟙 S) q
  simp only [Category.comp_id, Category.id_comp] at h₁
  have h₂ := composeMap_comp A B D T (𝟙 PLQ)
    (composeLeftRestrictionIso A B C E D F P Q).hom q
    (𝟙 ((BimoduleCategory.middleRightRestrictionFunctor A E D T F).obj R))
  simp only [Category.comp_id, Category.id_comp] at h₂
  have hi := h₁.symm.trans h₂
  have hm := composeMap_comp A B C T (𝟙 P) (𝟙 P)
    (composeMap A C D T (𝟙 LQc) q) (middleRestrictionComparisonMap A C E D T F Q₀ R₀)
  simp only [Category.id_comp] at hm
  have h := paste_square _ _ _ _ _ _ _ _ _ _ hi hs hn
  dsimp only [middleRestrictionResolvedMap]
  rw [hm]
  simp only [Category.assoc]
  convert h using 1 <;> rfl

end SerrePositivity.DifferentialGraded.BimoduleTensor
