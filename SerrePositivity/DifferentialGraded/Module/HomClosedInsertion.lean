module
public import SerrePositivity.DifferentialGraded.Module.Postcomposition
/-!
概要：斉次合成の中間の閉零加群射を、前の Hom の後合成と後の Hom の制限の間で移す。
方針：各評価の cochain に戻し、中間次数零の結合則を使う。
規約：全ての斉次次数と元の閉零射を保持する。
使われ方：bar の各 summand の包含を通じて二乗項を各列に移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

lemma moduleHomClosedInsertion {S M N P : ModuleCategory R D} (i : M ⟶ N)
    {p q n : ℤ}
    (f : (moduleHom R D (ForgetEnrichment.to (Complex R) S)
      (ForgetEnrichment.to (Complex R) M)).X p)
    (g : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) P)).X q) (h : p + q = n) :
    compose R (x := ForgetEnrichment.to (Complex R) S)
        (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) P)
        g ((eHomWhiskerLeft (Complex R) S i).f p f) h =
      compose R (x := ForgetEnrichment.to (Complex R) S)
        (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) P)
        ((eHomWhiskerRight (Complex R) i P).f q g) f h := by
  apply moduleHomElement_ext R D
    (M := ForgetEnrichment.to (Complex R) S) (N := ForgetEnrichment.to (Complex R) P)
  intro x
  rw [moduleHomCompose_π R D, moduleHomCompose_π R D,
    moduleHomWhiskerLeft_apply_π R D (T := S) (M := M) (N := N) i p f x,
    moduleHomWhiskerRight_apply_π R D (M := M) (N := N) (P := P) i q g x]
  exact Cochain.comp_assoc_of_second_is_zero_cochain _ _ _ h

end SerrePositivity.DifferentialGraded
