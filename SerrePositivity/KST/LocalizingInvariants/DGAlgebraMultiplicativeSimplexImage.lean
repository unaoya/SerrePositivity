module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingVertices
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMultiplicativeFrame
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathInvertingFunctor
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
概要：実乗法的単体は、擬同型を反転する関手の下で元の射の像を定める。
方針：元の単体射の像に実定数射の逆を後合成し、全単体制限との整合を示す。
規約：零単体の像は元の代数射の像。導来写像空間との同値は主張しない。
使われ方：導来比較の零次正規化と元の局所化射の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {C : Type v} [Category.{w} C]
  (L : Mon (Complex R) ⥤ C) (hL : InvertsQuasiIsos R L) {A B : Mon (Complex R)}

private lemma simplexImageCancel {U V W Z : C} (a : U ⟶ V) (i : Z ⟶ V)
    (j : Z ⟶ W) (t : V ⟶ W) [IsIso i] [IsIso j] (h : i ≫ t = j) :
    (a ≫ t) ≫ inv j = a ≫ inv i := by
  apply (cancel_mono j).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← h, IsIso.inv_hom_id_assoc]

def multiplicativeSimplexImage (n : SimplexCategoryᵒᵖ)
    (a : A ⟶ (multiplicativeSimplices R B).obj n) : L.obj A ⟶ L.obj B := by
  letI := hL ((multiplicativeSimplicesAugmentation R B).app n)
    (multiplicativeSimplicesAugmentation_quasiIso R B n)
  exact L.map a ≫ inv (L.map ((multiplicativeSimplicesAugmentation R B).app n))

lemma multiplicativeSimplexImage_constant (n : SimplexCategoryᵒᵖ) (f : A ⟶ B) :
    multiplicativeSimplexImage R L hL n
      (f ≫ (multiplicativeSimplicesAugmentation R B).app n) = L.map f := by
  letI := hL ((multiplicativeSimplicesAugmentation R B).app n)
    (multiplicativeSimplicesAugmentation_quasiIso R B n)
  unfold multiplicativeSimplexImage
  rw [L.map_comp, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

set_option maxHeartbeats 800000 in -- 全 AW 定数射の自然性を実関手の像で比較する。
lemma multiplicativeSimplexImage_restrict {m n : SimplexCategoryᵒᵖ} (θ : m ⟶ n)
    (a : A ⟶ (multiplicativeSimplices R B).obj m) :
    multiplicativeSimplexImage R L hL n (a ≫ (multiplicativeSimplices R B).map θ) =
      multiplicativeSimplexImage R L hL m a := by
  letI := hL ((multiplicativeSimplicesAugmentation R B).app n)
    (multiplicativeSimplicesAugmentation_quasiIso R B n)
  letI := hL ((multiplicativeSimplicesAugmentation R B).app m)
    (multiplicativeSimplicesAugmentation_quasiIso R B m)
  have hc : L.map ((multiplicativeSimplicesAugmentation R B).app m) ≫
      L.map ((multiplicativeSimplices R B).map θ) =
        L.map ((multiplicativeSimplicesAugmentation R B).app n) := by
    rw [← L.map_comp]
    have he := (multiplicativeSimplicesAugmentation R B).naturality θ
    change 𝟙 B ≫ (multiplicativeSimplicesAugmentation R B).app n =
      (multiplicativeSimplicesAugmentation R B).app m ≫
        (multiplicativeSimplices R B).map θ at he
    rw [Category.id_comp] at he
    exact congrArg L.map he.symm
  change L.map (a ≫ (multiplicativeSimplices R B).map θ) ≫
      inv (L.map ((multiplicativeSimplicesAugmentation R B).app n)) =
    L.map a ≫ inv (L.map ((multiplicativeSimplicesAugmentation R B).app m))
  rw [L.map_comp]
  exact simplexImageCancel (L.map a)
    (L.map ((multiplicativeSimplicesAugmentation R B).app m))
    (L.map ((multiplicativeSimplicesAugmentation R B).app n))
    (L.map ((multiplicativeSimplices R B).map θ)) hc

lemma multiplicativeSimplexImage_edge
    {x y : (multiplicativeMappingSimplices R A B) _⦋0⦌}
    (e : (multiplicativeMappingSimplices R A B).Edge x y) :
    multiplicativeSimplexImage R L hL (op ⦋0⦌) x =
      multiplicativeSimplexImage R L hL (op ⦋0⦌) y := by
  have hx := multiplicativeSimplexImage_restrict R L hL (SimplexCategory.δ (1 : Fin 2)).op e.edge
  have hy := multiplicativeSimplexImage_restrict R L hL (SimplexCategory.δ (0 : Fin 2)).op e.edge
  change multiplicativeSimplexImage R L hL (op ⦋0⦌)
    ((multiplicativeMappingSimplices R A B).δ 1 e.edge) = _ at hx
  change multiplicativeSimplexImage R L hL (op ⦋0⦌)
    ((multiplicativeMappingSimplices R A B).δ 0 e.edge) = _ at hy
  rw [e.src_eq] at hx
  rw [e.tgt_eq] at hy
  exact hx.trans hy.symm

def multiplicativeMappingPiZeroImage :
    SSet.π₀ (multiplicativeMappingSimplices R A B) → (L.obj A ⟶ L.obj B) :=
  SSet.π₀.lift (multiplicativeSimplexImage R L hL (op ⦋0⦌))
    (fun {_ _} e => multiplicativeSimplexImage_edge R L hL e)

lemma multiplicativeMappingPiZeroImage_original (f : A ⟶ B) :
    multiplicativeMappingPiZeroImage R L hL
      (SSet.π₀.mk (multiplicativeMappingVertexEquiv R A B f)) = L.map f := by
  change multiplicativeSimplexImage R L hL (op ⦋0⦌)
    (f ≫ (multiplicativeSimplicesAugmentation R B).app (op ⦋0⦌)) = _
  exact multiplicativeSimplexImage_constant R L hL (op ⦋0⦌) f

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
