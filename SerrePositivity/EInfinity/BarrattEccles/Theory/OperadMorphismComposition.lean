module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.OperadMorphismInsertion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionAdjacentFactor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionSquares
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilySplitNaturality

/-!
# オペラッド射と反復合成

## 概要
HA 3.2.4.7 の指定係数比較の増大のため、オペラッド射が反復合成を保つことを示す。

## 方針
最後の入力を分離し、一段の代入と残りの反復合成の可換正方形を合成する。

## 規約
零入力を含む任意の内側 arity の族と、未代入の尾を許す。

## 使われ方
実際の Barratt–Eccles の増大を零入力への係数射影に通す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Operad.Hom
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
open scoped BigOperators
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
variable {A : Type u} [CommRing A] {P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} (f : P ⟶ Q)

/-- オペラッド射の成分の有限テンソルは、最後の因子の分離と可換。 -/
@[reassoc]
lemma component_splitLast_naturality (n k : ℕ) (s : Fin (n + 1) → ℕ) :
    (f.map.app (FiniteBijection.of (n + 1 + k)) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap (n + 1) (fun j => f.map.app (FiniteBijection.of (s j)))) ≫
        (Q.arity (n + 1 + k) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => Q.arity (s j))).hom) =
    (P.arity (n + 1 + k) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => P.arity (s j))).hom) ≫
      (f.map.app (FiniteBijection.of (n + 1 + k)) ⊗ₘ
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun j => f.map.app (FiniteBijection.of (s j.castSucc))) ⊗ₘ
          f.map.app (FiniteBijection.of (s (Fin.last n))))) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.arity, SerrePositivity.SymmetricSequence.level]
  erw [tensorHom_comp_whiskerLeft, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_naturality,
    ← whiskerLeft_comp_tensorHom]

/-- オペラッド射は、指定した全入力への反復合成を保つ。 -/
lemma composeFirstInputs_naturality (n k : ℕ) (s : Fin n → ℕ) :
    (f.map.app (FiniteBijection.of (n + k)) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun j => f.map.app (FiniteBijection.of (s j)))) ≫
        Q.composeFirstInputs n k s =
    P.composeFirstInputs n k s ≫ f.map.app (FiniteBijection.of ((∑ j, s j) + k)) := by
  induction n generalizing k with
  | zero =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputs, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap, Fin.sum_univ_zero,
      eqToHom_refl, Category.comp_id, tensorHom_id]
    exact rightUnitor_naturality (f.map.app (FiniteBijection.of (0 + k)))
  | succ n ih =>
    have hstep := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_naturality
      (P.composeFirstInputInsertion n k (s (Fin.last n)))
      (P.composeFirstInputs n (k + s (Fin.last n)) (fun j => s j.castSucc))
      (Q.composeFirstInputInsertion n k (s (Fin.last n)))
      (Q.composeFirstInputs n (k + s (Fin.last n)) (fun j => s j.castSucc))
      (f.map.app (FiniteBijection.of (n + 1 + k)))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun j => f.map.app (FiniteBijection.of (s j.castSucc))))
      (f.map.app (FiniteBijection.of (s (Fin.last n))))
      (f.map.app (FiniteBijection.of (n + (k + s (Fin.last n)))))
      (f.map.app (FiniteBijection.of ((∑ j : Fin n, s j.castSucc) +
        (k + s (Fin.last n)))))
      (composeFirstInputInsertion_naturality f n k (s (Fin.last n)))
      (ih (k + s (Fin.last n)) (fun j => s j.castSucc))
    rw [P.composeFirstInputs_oneSlot_after_factor, Q.composeFirstInputs_oneSlot_after_factor]
    simp only [Category.assoc]
    rw [component_splitLast_naturality_assoc, reassoc_of% hstep,
      ← component_index_eq f (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.oneSlotComposeOutput_eq n k s)]

end SerrePositivity.EInfinity.Operad.Hom
