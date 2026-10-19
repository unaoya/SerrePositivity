module

public import SerrePositivity.KST.DerivedBlowup.AlgebraVertexFunctor
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-!
概要：KST v4 §3.1・Lemma 3.6（pp.11–14）の局所係数代数同型の一対象 dg 比較。
方針：指定 Hom 同型と一対象性を使い、順逆の合成と準同値を証明する。
規約：既存の一対象表示と局所の指定代数同型を保つ。
使われ方：係数図式同型の局所 perfect 性の保存・反映。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory DifferentialGraded

variable {R : Type u} [CommRing R] {A B : Mon (Complex R)}

/-- 概要：局所係数代数同型の一対象 dg 関手の順逆合成は恒等。
方針：一対象表示の合成保存と代数同型の逆条件を使う。
規約：KST Lemma 3.6。使われ方：指定局所 dg 比較の可逆性。 -/
theorem algebraVertexMap_hom_inv (e : A ≅ B) :
    (algebraVertexMap e.hom).comp (algebraVertexMap e.inv) = DGFunctor.id (AlgebraVertex A) := by
  rw [algebraVertexMap_comp, e.hom_inv_id, algebraVertexMap_id]

/-- 概要：局所係数代数同型の一対象表示は dg 準同値。
方針：全 Hom の複体同型性と標準点の本質的全射性を使う。
規約：KST §3.1・Lemma 3.6。使われ方：局所導来制限の perfect 性判定。 -/
theorem algebraVertexMap_quasiEquivalence (e : A ≅ B) :
    QuasiEquivalence (algebraVertexMap e.hom) := by
  constructor
  · intro x y
    change QuasiIso e.hom.hom
    infer_instance
  · apply Functor.essSurj_of_surj
    rintro ⟨x⟩
    change AlgebraVertex B at x
    cases x
    exact ⟨⟨AlgebraVertex.point⟩, rfl⟩

end SerrePositivity.KST.DerivedBlowup
