module
public import SerrePositivity.KST.SConstruction.DGHomGluingConeCochain

/-! # 元の右 cone 包含への三成分作用の制限
概要：同じ標準右包含への制限は、元の右成分を回収する。
方針：元の fst・snd への包含公式で左成分と第三成分を消す。
規約：第三成分の零性を仮定しない。使われ方：右 cone 閉同型による End 共役。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable {R : Type u} [CommRing R] {A B C D : Complex R}

/-- 標準右包含で制限すれば、比較ホモトピーを含む作用でも元の右成分だけが残る。 -/
lemma dgGluingConeCochain_inr (f : A ⟶ B) (g : C ⟶ D) {n m : ℤ}
    (a : Homogeneous A C n) (b : Homogeneous B D n) (h : Homogeneous A D m)
    (hm : m + 1 = n) :
    (Cochain.ofHom (mappingCone.inr f)).comp (dgGluingConeCochain f g a b h hm)
        (zero_add n) = b.comp (Cochain.ofHom (mappingCone.inr g)) (add_zero n) := by
  unfold dgGluingConeCochain mappingCone.liftCochain
  rw [Cochain.comp_add, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.comp_assoc_of_first_is_zero_cochain]
  simp only [Cochain.comp_units_smul, mappingCone.inr_fst_assoc,
    Cochain.zero_comp, smul_zero, zero_add,
    Cochain.comp_sub, mappingCone.inr_snd_assoc, sub_zero]

end SerrePositivity.KST.SConstruction
