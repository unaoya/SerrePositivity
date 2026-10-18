module
public import SerrePositivity.KST.ProExcision.NonUnitalHatGLComponents

/-!
# 非単位環の一般線形モノイドの群状性

概要：整数核の ĜL は π₀ の意味で群状であることを証明する。
方針：成分の逆行列の係数を零次へ持ち上げ、整数射影と積の式から核条件を得る。
規約：KST Claim 4.15。次数ごとの逆行列を仮定しない。
使われ方：Lemma A.4 の群状性の入力を外部仮定なしに供給する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open CategoryTheory Opposite SSet
open scoped Simplicial

/-- 概要：整数核の ĜL の頂点は逆成分の頂点を核内に持つ。
方針：成分環での逆行列を持ち上げ、積の整数射影が 1 であることを使う。
規約：KST Claim 4.15、単体次数での逆元ではなく成分での二側逆。
使われ方：群状性の実証明。 -/
lemma NonUnitalSimplicialRing.hatGL_inverse_vertex
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) (a : I.hatGLSubmonoid n 0) :
    ∃ b : I.hatGLSubmonoid n 0,
      I.hatGLClassMap n (π₀.mk b) = (I.hatGLClassMap n (π₀.mk a))⁻¹ := by
  let A := I.standardIdeal.ambient
  let g := I.hatGLClassMap n (π₀.mk a)
  have hs : ∀ i j : Fin n, ∃ b : A.obj (op ⦋0⦌),
      (π₀.mk b : π₀ (Comparison.ringSpace A)) = (g⁻¹).val i j :=
    fun i j ↦ @π₀.mk_surjective (Comparison.ringSpace A) ((g⁻¹).val i j)
  choose b hb using hs
  have hm : Comparison.matrixToComponents A n 0 b = (g⁻¹).val := by
    apply Matrix.ext
    intro i j
    rw [Comparison.matrixToComponents_zero_entry]
    exact hb i j
  have ha : Comparison.matrixToComponents A n 0 a.val = g.val := by
    change _ = a.property.1.unit.val
    exact a.property.1.unit_spec.symm
  have hprod : Comparison.matrixToComponents A n 0 a.val *
      Comparison.matrixToComponents A n 0 b = 1 := by
    rw [ha, hm]
    exact congrArg Units.val (mul_inv_cancel g)
  have hbFst : (Unitization.fstHom ℤ (I.obj (op ⦋0⦌))).mapMatrix b = 1 := by
    have h := congrArg I.componentsFst.mapMatrix hprod
    rw [map_mul, map_one, I.componentsFst_matrix, I.componentsFst_matrix,
      a.property.2, one_mul] at h
    exact h
  have hbUnit : b ∈ Comparison.hatGLSubmonoid A n 0 := by
    change IsUnit (Comparison.matrixToComponents A n 0 b)
    rw [hm]
    exact (g⁻¹).isUnit
  refine ⟨⟨b, hbUnit, hbFst⟩, ?_⟩
  apply Units.ext
  change hbUnit.unit.val = (g⁻¹).val
  rw [IsUnit.unit_spec]
  exact hm

/-- 概要：非単位単体環の ĜL は群状単体的モノイド。
方針：各成分の逆代表を構成し、成分比較の単射性で二側逆の法則を戻す。
規約：KST Claim 4.15、Segal 1974 Proposition 1.5 の群状性。
使われ方：Lemma 4.16 の実比較からの相対 bar 零化。 -/
lemma NonUnitalSimplicialRing.hatGL_isGrouplike
    (I : NonUnitalSimplicialRing.{u}) (n : ℕ) :
    Comparison.SimplicialMonoid.IsGrouplike (I.hatGL n) := by
  letI := Comparison.SimplicialMonoid.componentsMonoid (I.hatGL n)
  have hm (a b : I.hatGLSubmonoid n 0) :
      I.hatGLClassMap n (π₀.mk (a * b)) =
        I.hatGLClassMap n (π₀.mk a) * I.hatGLClassMap n (π₀.mk b) :=
    Comparison.hatGLVertexUnit_mul I.standardIdeal.ambient n
      ⟨a.val, a.property.1⟩ ⟨b.val, b.property.1⟩
  have h1 : I.hatGLClassMap n (π₀.mk (1 : I.hatGLSubmonoid n 0)) = 1 := by
    apply Units.ext
    change (1 : I.hatGLSubmonoid n 0).property.1.unit.val = 1
    rw [IsUnit.unit_spec]
    exact map_one _
  intro x
  induction x using π₀.rec with | mk a => ?_
  change I.hatGLSubmonoid n 0 at a
  obtain ⟨b, hb⟩ := I.hatGL_inverse_vertex n a
  refine ⟨⟨π₀.mk a, π₀.mk b, ?_, ?_⟩, rfl⟩
  · apply I.hatGLClassMap_injective n
    change I.hatGLClassMap n (π₀.mk (a * b)) = I.hatGLClassMap n (π₀.mk (1 : I.hatGLSubmonoid n 0))
    rw [hm, hb, mul_inv_cancel, h1]
  · apply I.hatGLClassMap_injective n
    change I.hatGLClassMap n (π₀.mk (b * a)) = I.hatGLClassMap n (π₀.mk (1 : I.hatGLSubmonoid n 0))
    rw [hm, hb, inv_mul_cancel, h1]

end SerrePositivity.KST.ProExcision
