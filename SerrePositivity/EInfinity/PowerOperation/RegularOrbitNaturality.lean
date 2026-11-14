module

public import SerrePositivity.EInfinity.PowerOperation.RegularOrbitCoordinates

/-!
# テンソル余不変の評価と実際の係数射

DAG XIII Construction 2.2.6 の orbit 比較の補助。
同じ余不変射で、係数の自然性と逆生成元の作用を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
variable {k G : Type u} [CommRing k] [CommGroup G]

lemma regularOrbitMap_left_mk {A B : Rep.{u} k G} (f : A ⟶ B) (x : A)
    (y : Rep.leftRegular k G) :
    (((Rep.coinvariantsTensor k G).map f).app (Rep.leftRegular k G)).hom
      (Rep.coinvariantsTensorMk A (Rep.leftRegular k G) x y) =
    Rep.coinvariantsTensorMk B (Rep.leftRegular k G) (f.hom x) y := by
  rfl

lemma regularOrbitMap_right_mk (A : Rep.{u} k G)
    (f : Rep.leftRegular k G ⟶ Rep.leftRegular k G) (x : A)
    (y : Rep.leftRegular k G) :
    (((Rep.coinvariantsTensor k G).obj A).map f).hom
      (Rep.coinvariantsTensorMk A (Rep.leftRegular k G) x y) =
    Rep.coinvariantsTensorMk A (Rep.leftRegular k G) x (f.hom y) := by
  rfl

/-- 同じ orbit の指定評価は、全係数射に自然。 -/
lemma regularOrbitEvaluation_natural {A B : Rep.{u} k G} (f : A ⟶ B)
    (x : ((Rep.coinvariantsTensor k G).obj A).obj (Rep.leftRegular k G)) :
    regularOrbitEvaluation B
      ((((Rep.coinvariantsTensor k G).map f).app (Rep.leftRegular k G)).hom x) =
    f.hom (regularOrbitEvaluation A x) := by
  obtain ⟨a, rfl⟩ := (regularOrbitEvaluation A).symm.surjective x
  rw [LinearEquiv.apply_symm_apply, regularOrbitEvaluation_symm,
    regularOrbitMap_left_mk, regularOrbitEvaluation_single]
  simp

/-- 余不変の評価は、解像度の生成元を係数の逆生成元へ送る。 -/
lemma regularOrbitEvaluation_action (A : Rep.{u} k G) (g : G)
    (x : ((Rep.coinvariantsTensor k G).obj A).obj (Rep.leftRegular k G)) :
    regularOrbitEvaluation A
      ((((Rep.coinvariantsTensor k G).obj A).map
        ((Rep.leftRegular k G).applyAsHom g)).hom x) =
    A.ρ g⁻¹ (regularOrbitEvaluation A x) := by
  obtain ⟨a, rfl⟩ := (regularOrbitEvaluation A).symm.surjective x
  rw [LinearEquiv.apply_symm_apply, regularOrbitEvaluation_symm, regularOrbitMap_right_mk]
  have h : ((Rep.leftRegular k G).applyAsHom g).hom (.single 1 1) =
      .single g 1 := by
    change Representation.ofMulAction k G G g (.single 1 1) = .single g 1
    simp [Representation.ofMulAction]
  rw [h]
  simpa using regularOrbitEvaluation_single A a g 1

end SerrePositivity.EInfinity.PowerOperation
