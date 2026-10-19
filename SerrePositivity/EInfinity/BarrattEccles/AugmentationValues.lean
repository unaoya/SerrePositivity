module

public import SerrePositivity.EInfinity.BarrattEccles.Contraction
public import SerrePositivity.EInfinity.BarrattEccles.Generators

/-!
# Barratt–Eccles の augmentation の生成元での値

概要：Berger–Fresse §1.1 の augmentation を0次の正規化生成元で計算する。
方針：正規化の射影と包含の合成が0次で恒等射であることを使う。
規約：各0単体は係数環の元1へ送られる。
使われ方：augmentation の単位と部分合成の保存を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory
open scoped Simplicial

variable (A : Type u) [CommRing A]

private lemma factorThru_arrow_apply {M N : ModuleCat A} (S : Subobject N) (f : M ⟶ N)
    (h : S.Factors f) (x : M) : S.arrow (S.factorThru f h x) = f x :=
  congrArg (fun φ => φ x) (Subobject.factorThru_arrow S f h)

/-- 概要：正規化鎖の augmentation は各0単体を1へ送る（Berger–Fresse §1.1.2）。
方針：収縮の順方向の射と正規化生成元を展開する。
規約：終域は0次の A である。
使われ方：複体の augmentation の生成元での値を与える。 -/
lemma normalizedAugmentation_generator_zero (n : ℕ) (x : (simplicial n) _⦋0⦌) :
    (normalizedChainContraction A n).hom.f 0 (normalizedGenerator A n 0 x) = (1 : A) := by
  simp only [normalizedChainContraction, HomotopyEquiv.trans_hom,
    HomologicalComplex.comp_f, ModuleCat.comp_apply]
  simp only [ChainComplex.single₀_obj_zero, SimplicialObject.Augmented.point_obj,
    AlgebraicTopology.alternatingFaceMapComplex_obj_X,
    AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex_hom,
    AlgebraicTopology.inclusionOfMooreComplexMap_f,
    AlgebraicTopology.NormalizedMooreComplex.objX_zero]
  erw [factorThru_arrow_apply A ⊤ _ (Subobject.top_factors _)]
  change (ModuleCat.FreeMonoidal.εIso A).inv
      (((ModuleCat.free A).map (Equiv.ofUnique (ULift.{u} PUnit.{1}) PUnit.{u + 1}).toIso.hom)
        (((ModuleCat.free A).map (↾fun _ : ULift.{u} ((simplicial n) _⦋0⦌) =>
          ULift.up PUnit.unit)) (ModuleCat.freeMk (ULift.up x)))) = (1 : A)
  erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply,
    ModuleCat.FreeMonoidal.εIso_inv_freeMk]

end SerrePositivity.EInfinity.BarrattEccles
