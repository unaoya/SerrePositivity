module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Morphism
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedCompositionEquivariance

/-!
# オペラッド射と反復合成の一段

## 概要
HA 3.2.4.7 の二色係数比較の増大を照合するため、オペラッド射を反復合成の一段に通す。

## 方針
arity の等式による移送、部分合成の保存、出力の移送の三つの可換正方形を合成する。

## 規約
全入力位置と零入力への代入を含む。

## 使われ方
零入力への係数射影が実際の増大を保つことの証明。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.Operad.Hom
open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded
attribute [local implicit_reducible] SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
variable {A : Type u} [CommRing A] {P Q : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A} (f : P ⟶ Q)

/-- オペラッド射の成分は arity の等式による移送と可換。 -/
@[reassoc]
lemma component_index_eq {r s : ℕ} (h : r = s) :
    eqToHom (congrArg P.arity h) ≫ f.map.app (FiniteBijection.of s) =
      f.map.app (FiniteBijection.of r) ≫ eqToHom (congrArg Q.arity h) := by
  subst s
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- 係数の arity の移送を、オペラッド射と内側の係数射のテンソルに通す。 -/
@[reassoc]
lemma component_tensor_index_eq {r s : ℕ} (h : r = s) (l : ℕ) :
    (f.map.app (FiniteBijection.of r) ⊗ₘ f.map.app (FiniteBijection.of l)) ≫
      (eqToHom (congrArg Q.arity h) ▷ Q.arity l) =
    (eqToHom (congrArg P.arity h) ▷ P.arity l) ≫
      (f.map.app (FiniteBijection.of s) ⊗ₘ f.map.app (FiniteBijection.of l)) := by
  simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp]
  rw [component_index_eq f h]
  congr 1

/-- 反復合成の一段は、オペラッド射に関して自然である。 -/
lemma composeFirstInputInsertion_naturality (n k l : ℕ) :
    (f.map.app (FiniteBijection.of (n + 1 + k)) ⊗ₘ f.map.app (FiniteBijection.of l)) ≫
      Q.composeFirstInputInsertion n k l =
    P.composeFirstInputInsertion n k l ≫ f.map.app (FiniteBijection.of (n + (k + l))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.composeFirstInputInsertion
  simp only [Category.assoc]
  rw [component_tensor_index_eq_assoc f (by omega : n + 1 + k = n + k + 1) l,
    ← reassoc_of% (f.comp (n + k) l ⟨n, by omega⟩),
    ← component_index_eq f (Nat.add_assoc n k l)]

end SerrePositivity.EInfinity.Operad.Hom
