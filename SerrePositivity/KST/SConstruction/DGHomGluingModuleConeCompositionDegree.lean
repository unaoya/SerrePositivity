module
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeComposition

/-! # 実 cone 合成の第三成分の次数指定
概要：同じ実 end 内の合成式で、第三成分の出力次数を明示的に指定する。
方針：元の合成式へ整数次数の等号で帰着する。
規約：比較成分を別の対象へ置換しない。使われ方：元の gluing 合成との照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]

/-- 同じ end 内の三成分作用は、第三成分の符号を保持する斉次合成式を満たす。 -/
lemma dgGluingModuleConeElement_comp_at {M N P Q T U : ModuleCategory R E}
    (f : M ⟶ N) (g : P ⟶ Q) (j : T ⟶ U) {n m p l o : ℤ}
    (a : (moduleHom R E (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) P)).X n)
    (b : (moduleHom R E (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) Q)).X n)
    (h : (moduleHom R E (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) Q)).X m) (hm : m + 1 = n)
    (c : (moduleHom R E (ForgetEnrichment.to (Complex R) P)
      (ForgetEnrichment.to (Complex R) T)).X p)
    (d : (moduleHom R E (ForgetEnrichment.to (Complex R) Q)
      (ForgetEnrichment.to (Complex R) U)).X p)
    (k : (moduleHom R E (ForgetEnrichment.to (Complex R) P)
      (ForgetEnrichment.to (Complex R) U)).X l) (hl : l + 1 = p)
    (ho : o + 1 = n + p) :
    compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R E f))
        (y := ForgetEnrichment.to (Complex R) (moduleCone R E g))
        (z := ForgetEnrichment.to (Complex R) (moduleCone R E j))
        (dgGluingModuleConeElement R E g j c d k hl)
        (dgGluingModuleConeElement R E f g a b h hm) rfl =
      dgGluingModuleConeElement R E f j (n := n + p) (m := o)
        (compose R (x := ForgetEnrichment.to (Complex R) M)
          (y := ForgetEnrichment.to (Complex R) P)
          (z := ForgetEnrichment.to (Complex R) T) c a rfl)
        (compose R (x := ForgetEnrichment.to (Complex R) N)
          (y := ForgetEnrichment.to (Complex R) Q)
          (z := ForgetEnrichment.to (Complex R) U) d b rfl)
        (compose R (x := ForgetEnrichment.to (Complex R) M)
            (y := ForgetEnrichment.to (Complex R) P)
            (z := ForgetEnrichment.to (Complex R) U) k a (by omega : n + l = o) +
          p.negOnePow • compose R (x := ForgetEnrichment.to (Complex R) M)
            (y := ForgetEnrichment.to (Complex R) Q)
            (z := ForgetEnrichment.to (Complex R) U) d h (by omega : m + p = o)) (by omega) := by
  have he : m + p = o := by omega
  cases he
  exact dgGluingModuleConeElement_comp R E f g j a b h hm c d k hl

end SerrePositivity.KST.SConstruction
