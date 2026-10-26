module
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeElement
public import SerrePositivity.KST.SConstruction.DGHomGluingConeConnectingCochain
public import SerrePositivity.DifferentialGraded.Module.ShiftHom
public import SerrePositivity.DifferentialGraded.Module.ConeMaps

/-!
概要：実加群 cone の connecting 射は元の三成分全 Hom 作用について自然。
方針：元 Hom end の全評価で同じ三成分複体計算へ戻す。
規約：第三 cochain と全次数を保持。使われ方：逆回転の全 dg 自然性の証明。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]

/-- 概要：元三成分の実加群 Hom 元は同じ connecting 射に全次数で可換。
方針：元 end の評価と同じ target shift の全 Hom 比較を使う。
規約：元の加群射の等号。使われ方：全 cone 関手の閉零比較の自然性。 -/
lemma dgGluingModuleConeElement_connecting {M N P Q : ModuleCategory R E}
    (f : M ⟶ N) (g : P ⟶ Q) {n m : ℤ}
    (a : (moduleHom R E (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) P)).X n)
    (b : (moduleHom R E (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) Q)).X n)
    (h : (moduleHom R E (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) Q)).X m) (hm : m + 1 = n) :
    (eHomWhiskerLeft (Complex R) (moduleCone R E f) (moduleConeConnecting R E g)).f n
        (dgGluingModuleConeElement R E f g a b h hm) =
      (eHomWhiskerRight (Complex R) (moduleConeConnecting R E f) (P⟦(1 : ℤ)⟧)).f n
        ((moduleShiftHom R E 1 (ForgetEnrichment.to (Complex R) M)
          (ForgetEnrichment.to (Complex R) P)).f n a) := by
  apply moduleHomElement_ext R E
    (M := ForgetEnrichment.to (Complex R) (moduleCone R E f))
    (N := shiftModule 1 (ForgetEnrichment.to (Complex R) P))
  intro x
  apply (moduleHomWhiskerLeft_apply_π R E (T := moduleCone R E f)
    (moduleConeConnecting R E g) n (dgGluingModuleConeElement R E f g a b h hm) x).trans
  apply Eq.trans _ (moduleHomWhiskerRight_apply_π R E (P := P⟦(1 : ℤ)⟧)
    (moduleConeConnecting R E f) n ((moduleShiftHom R E 1
      (ForgetEnrichment.to (Complex R) M) (ForgetEnrichment.to (Complex R) P)).f n a) x).symm
  rw [dgGluingModuleConeElement_π, moduleConeConnecting_eval, moduleConeConnecting_eval]
  have hs := congrArg (fun k => k.f n a)
    (moduleShiftHom_π R E 1 (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) P) x)
  change (moduleHomπ R E (shiftModule 1 (ForgetEnrichment.to (Complex R) M))
      (shiftModule 1 (ForgetEnrichment.to (Complex R) P)) x).f n
        ((moduleShiftHom R E 1 (ForgetEnrichment.to (Complex R) M)
          (ForgetEnrichment.to (Complex R) P)).f n a) = _ at hs
  apply (dgGluingConeCochain_connecting _ _ _ _ _ hm).trans
  exact congrArg (fun c => (Cochain.ofHom
    (mappingCone.triangle ((moduleEvaluation R E x).map f)).mor₃).comp c (zero_add n)) hs.symm
end SerrePositivity.KST.SConstruction
