module
public import SerrePositivity.DifferentialGraded.Module.Postcomposition

/-!
概要：全次数の加群 Hom の斉次合成は、閉零射による後合成と両立する。
方針：各加群評価の cochain へ戻し、次数零の第三射との結合則を使う。
規約：元の加群と全次数を保持する。
使われ方：bar のシフトブロックを元の余積包含へ送る計算。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleHomPostcomposition_compose {S M N P : ModuleCategory R D} (i : N ⟶ P)
    {p q n : ℤ}
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) S)
      (ForgetEnrichment.to (Complex R) M)).X p)
    (g : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N)).X q) (h : p + q = n) :
    compose R (x := ForgetEnrichment.to (Complex R) S)
      (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) P)
      ((eHomWhiskerLeft (Complex R) M i).f q g) f h =
    (eHomWhiskerLeft (Complex R) S i).f n
      (compose R (x := ForgetEnrichment.to (Complex R) S)
        (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) N)
        g f h) := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) S) (N := ForgetEnrichment.to (Complex R) P)
  intro x
  rw [moduleHomCompose_π R D,
    moduleHomWhiskerLeft_apply_π R D (T := M) (M := N) (N := P) i q g x,
    moduleHomWhiskerLeft_apply_π R D (T := S) (M := N) (N := P) i n
      (compose R (x := ForgetEnrichment.to (Complex R) S)
        (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) N) g f h) x,
    moduleHomCompose_π R D]
  exact (Cochain.comp_assoc_of_third_is_zero_cochain
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) S)
      (ForgetEnrichment.to (Complex R) M) x).f p f)
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N) x).f q g)
    (Cochain.ofHom ((moduleEvaluation R D x).map i)) h).symm

end SerrePositivity.DifferentialGraded
