module
public import SerrePositivity.DifferentialGraded.Module.Postcomposition
/-!
概要：閉零加群射による全次数 Hom の制限は通常順の斉次合成と可換。
方針：元の評価成分へ戻し、次数零 cochain を先頭に置く結合則を使う。
規約：元の閉射と全次数 Hom を保持し、h 圏だけの等式には弱めない。
使われ方：coherent bar の MC 方程式を各 summand の列へ制限する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleHomRestriction_compose {S M N P : ModuleCategory R D} (i : S ⟶ M)
    {p q n : ℤ}
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) N)).X p)
    (g : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) P)).X q) (h : p + q = n) :
    (eHomWhiskerRight (Complex R) i P).f n
        (compose R (x := ForgetEnrichment.to (Complex R) M)
          (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) P)
          g f h) =
      compose R (x := ForgetEnrichment.to (Complex R) S)
        (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) P)
        g ((eHomWhiskerRight (Complex R) i N).f p f) h := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) S) (N := ForgetEnrichment.to (Complex R) P)
  intro x
  rw [moduleHomWhiskerRight_apply_π R D (M := S) (N := M) (P := P) i n _ x,
    moduleHomCompose_π R D (T := ForgetEnrichment.to (Complex R) M)
      (M := ForgetEnrichment.to (Complex R) N) (N := ForgetEnrichment.to (Complex R) P),
    moduleHomCompose_π R D (T := ForgetEnrichment.to (Complex R) S)
      (M := ForgetEnrichment.to (Complex R) N) (N := ForgetEnrichment.to (Complex R) P),
    moduleHomWhiskerRight_apply_π R D (M := S) (N := M) (P := N) i p _ x]
  exact (Cochain.comp_assoc_of_first_is_zero_cochain _ _ _ h).symm

end SerrePositivity.DifferentialGraded
