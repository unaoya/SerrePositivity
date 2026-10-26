module
public import SerrePositivity.KST.SConstruction.DGConeDescCochainNaturality

/-!
概要：元実 cone への指定二成分 lift の全次数自然性を検出する。
方針：元左右射影で全 cochain を照合し、次数一成分の符号を二度の作用で消す。
規約：元の二成分を保持。使われ方：回転比較の実 cone lift を全関手族へ束ねる。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable {R : Type u} [CommRing R] {A B C D E E' : Complex R}

/-- 概要：元二成分の全自然性は同じ cone lift の全 Hom 自然性を与える。
方針：元左右射影の厳密回収と同じ Koszul 符号を照合する。
規約：全整数次数での等号。使われ方：実回転比較の全自然性。 -/
lemma dgConeLiftCochain_naturality (f : A ⟶ B) (g : C ⟶ D) {n : ℤ}
    (a : Homogeneous A C n) (b : Homogeneous B D n) (c : Homogeneous E E' n)
    (h : Homogeneous E A 1) (h' : Homogeneous E' C 1)
    (q : Homogeneous E B 0) (q' : Homogeneous E' D 0)
    (hh : h.comp a (add_comm 1 n) = n.negOnePow • c.comp h' rfl)
    (hq : q.comp b (zero_add n) = c.comp q' (add_zero n)) :
    (mappingCone.liftCochain f h q rfl).comp (coneMapCochain f g a b) (zero_add n) =
      c.comp (mappingCone.liftCochain g h' q' rfl) (add_zero n) := by
  have hh' : n.negOnePow • h.comp a (add_comm 1 n) = c.comp h' rfl := by
    simpa only [smul_smul, Int.units_mul_self, one_smul] using
      congrArg (fun t => n.negOnePow • t) hh
  apply (mappingCone.ext_cochain_to_iff g n (n + 1) rfl).2
  constructor
  · calc
      _ = (mappingCone.liftCochain f h q rfl).comp
          ((coneMapCochain f g a b).comp (mappingCone.fst g).val rfl) (zero_add (n + 1)) :=
        Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ rfl
      _ = (mappingCone.liftCochain f h q rfl).comp
          (n.negOnePow • (mappingCone.fst f).val.comp a (add_comm 1 n)) (zero_add (n + 1)) :=
        congrArg (fun t => (mappingCone.liftCochain f h q rfl).comp t (zero_add (n + 1)))
          (coneMapCochain_fst f g a b)
      _ = n.negOnePow • h.comp a (add_comm 1 n) := by
        rw [Cochain.comp_units_smul, ← Cochain.comp_assoc_of_first_is_zero_cochain,
          mappingCone.liftCochain_fst]
      _ = c.comp h' rfl := hh'
      _ = c.comp ((mappingCone.liftCochain g h' q' rfl).comp (mappingCone.fst g).val rfl) rfl := by
        rw [mappingCone.liftCochain_fst]
      _ = _ := (Cochain.comp_assoc_of_second_is_zero_cochain _ _ _ rfl).symm
  · calc
      _ = (mappingCone.liftCochain f h q rfl).comp
          ((coneMapCochain f g a b).comp (mappingCone.snd g) (add_zero n)) (zero_add n) :=
        Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ (add_zero n)
      _ = (mappingCone.liftCochain f h q rfl).comp
          ((mappingCone.snd f).comp b (zero_add n)) (zero_add n) :=
        congrArg (fun t => (mappingCone.liftCochain f h q rfl).comp t (zero_add n))
          (coneMapCochain_snd f g a b)
      _ = q.comp b (zero_add n) := by
        rw [← Cochain.comp_assoc_of_first_is_zero_cochain, mappingCone.liftCochain_snd]
      _ = c.comp q' (add_zero n) := hq
      _ = c.comp ((mappingCone.liftCochain g h' q' rfl).comp (mappingCone.snd g) (add_zero 0))
          (add_zero n) := by rw [mappingCone.liftCochain_snd]
      _ = _ := (Cochain.comp_assoc_of_second_is_zero_cochain _ _ _ (add_zero n)).symm
end SerrePositivity.KST.SConstruction
