module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackDiagonal
public import SerrePositivity.KST.LocalizingInvariants.CochainCoconeTriangleMap
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：実経路模型の両射影の共通核を、元の差の cocone の接続射で記述する。
方針：実複体同型を標準 cocone 三角形のホモロジー完全列に適用する。
規約：比較は元の二脚を保持する。使われ方：対角射の pro 核・像判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex CochainComplex Pretriangulated
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] {A B C : Mon (Complex R)} (f : A ⟶ B) (g : C ⟶ B)

def connecting (n : ℤ) : B.X.homology (n - 1) ⟶ (algebra R f g).X.homology n :=
  homologyδOfTriangle (mappingCocone.triangle (difference R f g)) (n - 1) n (by omega) ≫
    homologyMap (complexIso R f g).inv n

lemma homology_biprod_zero_iff (K L : Complex R) (n : ℤ)
    (x : (K ⊞ L).homology n) :
    homologyMap (biprod.fst : K ⊞ L ⟶ K) n x = 0 ∧
      homologyMap (biprod.snd : K ⊞ L ⟶ L) n x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    let H := homologyFunctor (ModuleCat R) (.up ℤ) n
    have ht : H.map (biprod.fst : K ⊞ L ⟶ K) ≫ H.map biprod.inl +
        H.map (biprod.snd : K ⊞ L ⟶ L) ≫ H.map biprod.inr = 𝟙 _ := by
      rw [← H.map_comp, ← H.map_comp, ← H.map_add, biprod.total, H.map_id]
    have he := congrArg (fun t : H.obj (K ⊞ L) ⟶ H.obj (K ⊞ L) => t x) ht
    change homologyMap (biprod.inl : K ⟶ K ⊞ L) n
        (homologyMap (biprod.fst : K ⊞ L ⟶ K) n x) +
      homologyMap (biprod.inr : L ⟶ K ⊞ L) n
        (homologyMap (biprod.snd : K ⊞ L ⟶ L) n x) = x at he
    simpa only [hx.1, hx.2, map_zero, zero_add] using he.symm
  · rintro rfl
    exact ⟨map_zero _, map_zero _⟩

lemma connecting_pair_exact (n : ℤ) (x : (algebra R f g).X.homology n) :
    homologyMap (left R f g).hom n x = 0 ∧ homologyMap (right R f g).hom n x = 0 ↔
      ∃ z : B.X.homology (n - 1), connecting R f g n z = x := by
  let e := complexIso R f g
  let δ := homologyδOfTriangle (mappingCocone.triangle (difference R f g))
    (n - 1) n (by omega)
  have hS := homologyMap_exact₁_of_distTriang (mappingCocone.triangle (difference R f g))
    (DerivedCategory.mappingCocone_triangle_distinguished _) (n - 1) n (by omega)
  have he : Function.Exact δ (homologyMap (mappingCocone.fst (difference R f g)) n) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 hS
  have hp : homologyMap (mappingCocone.fst (difference R f g)) n (homologyMap e.hom n x) = 0 ↔
      homologyMap (left R f g).hom n x = 0 ∧ homologyMap (right R f g).hom n x = 0 := by
    rw [← homology_biprod_zero_iff R A.X C.X n]
    have hl := toMappingCocone_left R f g
    have hr := toMappingCocone_right R f g
    simp only [e, complexIso, ← ModuleCat.comp_apply, ← homologyMap_comp,
      Category.assoc, hl, hr]
  rw [← hp, he]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    change homologyMap e.inv n (δ z) = x
    rw [hz, ← ModuleCat.comp_apply, ← homologyMap_comp, e.hom_inv_id, homologyMap_id]
    rfl
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have hh := congrArg (fun y => homologyMap e.hom n y) hz
    change homologyMap e.hom n (homologyMap e.inv n (δ z)) = homologyMap e.hom n x at hh
    simpa only [← ModuleCat.comp_apply, ← homologyMap_comp, e.inv_hom_id,
      homologyMap_id, ModuleCat.id_apply] using hh

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.HomotopyPullbackModel
