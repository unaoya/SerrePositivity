module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.LaxTensorComparison
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Basic

/-!
# Lax braided 関手によるオペラッドの移送

## 概要
Berger–Moerdijk §1 の対称オペラッドを、複体間の lax braided 関手で送る。

## 方針
構造射の比較四角形を合成し、単位・置換・結合の各等式を移す。

## 規約
arity の等式による移送と Koszul 対称性を保持する。

## 使われ方
セル代数の次数付きの台を与えるオペラッドの構成。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory DifferentialGraded
open Functor.LaxMonoidal

namespace LaxComparisonSquare

variable {S T : Type u} [CommRing S] [CommRing T]
  (F : Complex S ⥤ Complex T) [F.LaxBraided]

omit [F.LaxBraided] in
/-- Equal original paths give equal image paths when the target comparison is an identity. -/
lemma paths {X Y : Complex S} {X' : Complex T} (a : X' ⟶ F.obj X)
    {f g : X ⟶ Y} {f' g' : X' ⟶ F.obj Y}
    (hf : LaxComparisonSquare F a (𝟙 _) f' f)
    (hg : LaxComparisonSquare F a (𝟙 _) g' g) (h : f = g) : f' = g' := by
  unfold LaxComparisonSquare at hf hg
  simpa only [Category.comp_id] using
    hf.trans ((congrArg (fun k => a ≫ F.map k) h).trans hg.symm)

/-- The image of a unit constraint has the specified unit comparison. -/
lemma image_leftUnitor (X : Complex S) :
    LaxComparisonSquare F (laxTensorComparison F (ε F) (𝟙 (F.obj X))) (𝟙 _)
      (λ_ (F.obj X)).hom (λ_ X).hom := by
  simp only [LaxComparisonSquare, laxTensorComparison, tensorHom_def',
    whiskerLeft_id, Category.comp_id, Category.id_comp, Category.assoc]
  exact left_unitality F X

/-- The image of a right unit constraint has the specified unit comparison. -/
lemma image_rightUnitor (X : Complex S) :
    LaxComparisonSquare F (laxTensorComparison F (𝟙 (F.obj X)) (ε F)) (𝟙 _)
      (ρ_ (F.obj X)).hom (ρ_ X).hom := by
  simp only [LaxComparisonSquare, laxTensorComparison, tensorHom_def',
    id_whiskerRight, Category.comp_id, Category.assoc]
  exact right_unitality F X

end LaxComparisonSquare

namespace Operad
variable {S T : Type u} [CommRing S] [CommRing T]
  (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad S) (F : Complex S ⥤ Complex T) [F.LaxBraided]

/-- The transported partial composition, with its specified tensor comparison. -/
def monoidalImageComp (m n : ℕ) (i : Fin (m + 1)) :
    F.obj (P.arity (m + 1)) ⊗ F.obj (P.arity n) ⟶ F.obj (P.arity (m + n)) :=
  μ F _ _ ≫ F.map (P.comp m n i)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (monoidalImageComp)


lemma monoidalImageComp_square (m n : ℕ) (i : Fin (m + 1)) :
    LaxComparisonSquare F (laxTensorComparison F (𝟙 _) (𝟙 _)) (𝟙 _)
      (P.monoidalImageComp F m n i) (P.comp m n i) := by
  simp [LaxComparisonSquare, laxTensorComparison, monoidalImageComp]

lemma monoidalImageUnit_square :
    LaxComparisonSquare F (ε F) (𝟙 _) (ε F ≫ F.map P.unit) P.unit := by
  simp [LaxComparisonSquare]

omit [F.LaxBraided] in
lemma monoidalImageCast_square {m n : ℕ} (h : m = n) :
    LaxComparisonSquare F (𝟙 _) (𝟙 _)
      (eqToHom (congrArg (fun k => F.obj (P.arity k)) h))
      (eqToHom (congrArg P.arity h)) := by
  cases h
  simp [LaxComparisonSquare]

lemma monoidalImageTensorCast_square {m n : ℕ} (h : m = n) (k : ℕ) :
    LaxComparisonSquare F (laxTensorComparison F (𝟙 _) (𝟙 _))
      (laxTensorComparison F (𝟙 _) (𝟙 _))
      (eqToHom (congrArg (fun q => F.obj (P.arity q) ⊗ F.obj (P.arity k)) h))
      (eqToHom (congrArg (fun q => P.arity q ⊗ P.arity k) h)) := by
  cases h
  simp [LaxComparisonSquare]

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (monoidalImageComp_square monoidalImageUnit_square monoidalImageCast_square monoidalImageTensorCast_square)


/-- A lax braided functor sends a symmetric operad to a symmetric operad. -/
def monoidalImage : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad T where
  sequence := P.sequence ⋙ F
  unit := ε F ≫ F.map P.unit
  comp := P.monoidalImageComp F
  unit_comp n := by
    have h₁ := LaxComparisonSquare.comp F
      (LaxComparisonSquare.whiskerRight F (𝟙 (F.obj (P.arity n)))
        (P.monoidalImageUnit_square F))
      (LaxComparisonSquare.comp F (P.monoidalImageComp_square F 0 n 0)
        (P.monoidalImageCast_square F (Nat.zero_add n)))
    exact LaxComparisonSquare.paths F _ h₁
      (LaxComparisonSquare.image_leftUnitor F (P.arity n)) (P.unit_comp n)
  comp_unit m i := by
    have h₁ := LaxComparisonSquare.comp F
      (LaxComparisonSquare.whiskerLeft F (𝟙 (F.obj (P.arity (m + 1))))
        (P.monoidalImageUnit_square F))
      (P.monoidalImageComp_square F m 1 i)
    exact LaxComparisonSquare.paths F _ h₁
      (LaxComparisonSquare.image_rightUnitor F (P.arity (m + 1))) (P.comp_unit m i)
  inner_equivariance m n i τ := by
    have hp' : LaxComparisonSquare F (𝟙 _) (𝟙 _)
        (F.map (P.sequence.map (FiniteBijection.permutation n τ)))
        (P.sequence.map (FiniteBijection.permutation n τ)) := by
      simp [LaxComparisonSquare]
    have h₁ := LaxComparisonSquare.comp F
      (LaxComparisonSquare.whiskerLeft F (𝟙 (F.obj (P.arity (m + 1)))) hp')
      (P.monoidalImageComp_square F m n i)
    have h₂ := LaxComparisonSquare.comp F (P.monoidalImageComp_square F m n i)
      (show LaxComparisonSquare F (𝟙 _) (𝟙 _)
        (F.map (P.sequence.map (FiniteBijection.permutation (m + n)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ))))
        (P.sequence.map (FiniteBijection.permutation (m + n)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i τ))) by simp [LaxComparisonSquare])
    exact LaxComparisonSquare.paths F _ h₁ h₂ (P.inner_equivariance m n i τ)
  outer_equivariance m n i σ := by
    have hp : LaxComparisonSquare F (𝟙 _) (𝟙 _)
        (F.map (P.sequence.map (FiniteBijection.permutation (m + 1) σ)))
        (P.sequence.map (FiniteBijection.permutation (m + 1) σ)) := by
      simp [LaxComparisonSquare]
    have h₁ := LaxComparisonSquare.comp F
      (LaxComparisonSquare.whiskerRight F (𝟙 (F.obj (P.arity n))) hp)
      (P.monoidalImageComp_square F m n (σ i))
    have h₂ := LaxComparisonSquare.comp F (P.monoidalImageComp_square F m n i)
      (show LaxComparisonSquare F (𝟙 _) (𝟙 _)
        (F.map (P.sequence.map (FiniteBijection.permutation (m + n)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ))))
        (P.sequence.map (FiniteBijection.permutation (m + n)
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i σ))) by simp [LaxComparisonSquare])
    exact LaxComparisonSquare.paths F _ h₁ h₂ (P.outer_equivariance m n i σ)
  nested_assoc m n k i j := by
    let a := 𝟙 (F.obj (P.arity (m + 1)))
    let b := 𝟙 (F.obj (P.arity (n + 1)))
    let d := 𝟙 (F.obj (P.arity k))
    have h₁ := LaxComparisonSquare.comp F
      (LaxComparisonSquare.whiskerRight F d (P.monoidalImageComp_square F m (n + 1) i))
      (P.monoidalImageComp_square F (m + n) k ⟨i.val + j.val, by omega⟩)
    have h₂ := LaxComparisonSquare.comp F (LaxComparisonSquare.associator F a b d)
      (LaxComparisonSquare.comp F
        (LaxComparisonSquare.whiskerLeft F a (P.monoidalImageComp_square F n k j))
        (LaxComparisonSquare.comp F (P.monoidalImageComp_square F m (n + k) i)
          (P.monoidalImageCast_square F (Nat.add_assoc m n k).symm)))
    exact LaxComparisonSquare.paths F _ h₁ h₂ (P.nested_assoc m n k i j)
  parallel_assoc m n k i j hij := by
    let a := 𝟙 (F.obj (P.arity (m + 2)))
    let b := 𝟙 (F.obj (P.arity n))
    let d := 𝟙 (F.obj (P.arity k))
    have h₁ := LaxComparisonSquare.comp F
      (LaxComparisonSquare.whiskerRight F d (P.monoidalImageComp_square F (m + 1) n i))
      (LaxComparisonSquare.comp F
        (P.monoidalImageTensorCast_square F (by omega : m + 1 + n = m + n + 1) k)
        (P.monoidalImageComp_square F (m + n) k ⟨j.val + n - 1, by omega⟩))
    have h₂ := LaxComparisonSquare.comp F (LaxComparisonSquare.associator F a b d)
      (LaxComparisonSquare.comp F
        (LaxComparisonSquare.whiskerLeft F a (LaxComparisonSquare.braiding F b d))
        (LaxComparisonSquare.comp F
          (LaxComparisonSquare.iso_inv F (LaxComparisonSquare.associator F a d b))
          (LaxComparisonSquare.comp F
            (LaxComparisonSquare.whiskerRight F b
              (P.monoidalImageComp_square F (m + 1) k j))
            (LaxComparisonSquare.comp F
              (P.monoidalImageTensorCast_square F (by omega : m + 1 + k = m + k + 1) n)
              (LaxComparisonSquare.comp F
                (P.monoidalImageComp_square F (m + k) n ⟨i.val, by omega⟩)
                (P.monoidalImageCast_square F (by omega : m + k + n = m + n + k)))))))
    exact LaxComparisonSquare.paths F _ h₁ h₂ (P.parallel_assoc m n k i j hij)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
  export _root_.SerrePositivity.EInfinity.Operad (monoidalImage)


end Operad
end SerrePositivity.EInfinity
