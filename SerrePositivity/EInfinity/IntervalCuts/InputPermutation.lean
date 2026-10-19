module

public import SerrePositivity.EInfinity.IntervalCuts.ComponentPermutation
public import SerrePositivity.EInfinity.IntervalCuts.InputLinearIdentities
public import SerrePositivity.EInfinity.Surjection.Sequence

/-!
# 実際の区間入力の置換等変性

概要：Berger–Fresse §2.2.6 の全射語成分の等変性を区間の任意の入力へ移す。
方針：区間の二頂点・一辺で線形写像を比較し、χ の整数置換成分も評価する。
規約：全 arity・全語次数で選択した生成元以外の入力も含める。
使われ方：余演算の全整数双線形成分の等変性。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.IntervalCuts

open CategoryTheory MonoidalCategory HomologicalComplex Surjection
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

variable (A : Type u) [CommRing A]

/-- 概要：実際の任意の頂点次数入力の双線形余演算は置換と両立（BF §2.2.6）。
方針：二頂点の外延性で語加群の線形等変性へ戻す。
規約：第一入力は語加群の任意の元。
使われ方：整数成分の頂点入力分岐。 -/
lemma vertexInputBilinear_permutation (n d : ℕ) (σ : Equiv.Perm (Fin n))
    (x : degreeModule A n d) :
    vertexInputBilinear A n d (renameLinear A σ x) =
      ((permutationAction (interval A) n σ).asIso.hom.f (-(d : ℤ))).hom.comp
        (vertexInputBilinear A n d x) := by
  have h : ModuleCat.ofHom (vertexInputBilinear A n d (renameLinear A σ x)) =
      ModuleCat.ofHom (((permutationAction (interval A) n σ).asIso.hom.f (-(d : ℤ))).hom.comp
        (vertexInputBilinear A n d x)) := by
    apply vertexInput_hom_ext A
    intro b
    change vertexInputBilinear A n d (renameLinear A σ x)
      ((intervalXIso A 0).inv (vertexChain A b)) =
        (permutationAction (interval A) n σ).asIso.hom.f (-(d : ℤ))
          (vertexInputBilinear A n d x ((intervalXIso A 0).inv (vertexChain A b)))
    rw [vertexInputBilinear_vertex, vertexInputBilinear_vertex]
    exact congrArg (fun f : degreeModule A n d →ₗ[A]
      (power (interval A) n).X (-(d : ℤ)) => f x) (vertexComponent_permutation A n d σ b)
  exact congrArg (fun f => f.hom) h

/-- 概要：実際の任意の辺次数入力の双線形余演算は置換と両立（BF §2.2.6）。
方針：一辺の外延性で語加群の線形等変性へ戻す。
規約：全 arity・全語次数。
使われ方：整数成分の辺入力分岐。 -/
lemma edgeInputBilinear_permutation (n d : ℕ) (σ : Equiv.Perm (Fin n))
    (x : degreeModule A n d) :
    edgeInputBilinear A n d (renameLinear A σ x) =
      ((permutationAction (interval A) n σ).asIso.hom.f (-((d + 1 : ℕ) : ℤ))).hom.comp
        (edgeInputBilinear A n d x) := by
  have h : ModuleCat.ofHom (edgeInputBilinear A n d (renameLinear A σ x)) =
      ModuleCat.ofHom (((permutationAction (interval A) n σ).asIso.hom.f
        (-((d + 1 : ℕ) : ℤ))).hom.comp (edgeInputBilinear A n d x)) := by
    apply edgeInput_hom_ext A
    change edgeInputBilinear A n d (renameLinear A σ x) ((intervalXIso A 1).inv (edgeChain A)) =
      (permutationAction (interval A) n σ).asIso.hom.f (-((d + 1 : ℕ) : ℤ))
        (edgeInputBilinear A n d x ((intervalXIso A 1).inv (edgeChain A)))
    rw [edgeInputBilinear_edge, edgeInputBilinear_edge]
    exact congrArg (fun f : degreeModule A n d →ₗ[A]
      (power (interval A) n).X (-((d + 1 : ℕ) : ℤ)) => f x) (edgeComponent_permutation A n d σ)
  exact congrArg (fun f => f.hom) h

/-- 概要：χ の整数負次数の置換は次数比較後に語の置換となる（BF §1.2.1）。
方針：零延長の射の成分公式と比較同型の逆性を使う。
規約：自然数語次数 d は整数 −d。
使われ方：整数余演算の置換を既存の双線形等変性へ戻す。 -/
lemma complexRename_neg_hom_apply (n d : ℕ) (σ : Equiv.Perm (Fin n))
    (x : (complex A n).X (-(d : ℤ))) :
    (complexXIso A n d).hom ((complexRename A n σ).f (-(d : ℤ)) x) =
      renameLinear A σ ((complexXIso A n d).hom x) := by
  have h := extendMap_f (normalizedRename A n σ) ComplexShape.embeddingDownNat (i := d) rfl
  change (complexRename A n σ).f (-(d : ℤ)) =
    (complexXIso A n d).hom ≫ ModuleCat.ofHom (renameLinear A σ) ≫
      (complexXIso A n d).inv at h
  rw [h]
  exact (complexXIso A n d).toLinearEquiv.apply_symm_apply _

end SerrePositivity.EInfinity.IntervalCuts
