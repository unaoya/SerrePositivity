module
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeElement

/-! # 実加群 Hom 内の三成分 cone 作用の微分
概要：実 end 内の三成分作用の線形性と捻れた微分式を証明する。
方針：全評価の単射性で元の cochain の既証明へ帰着する。
規約：比較差を消す仮定を置かない。使われ方：元の gluing Hom からの鎖写像。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]

/-- 実 end 内の同じ三成分作用は加法を保存する。 -/
lemma dgGluingModuleConeElement_add {M N P Q : ModuleCategory R E}
    (f : M ⟶ N) (g : P ⟶ Q) {n m : ℤ} (a a') (b b') (h h') (hm : m + 1 = n) :
    dgGluingModuleConeElement R E f g (a + a') (b + b') (h + h') hm =
      dgGluingModuleConeElement R E f g a b h hm +
        dgGluingModuleConeElement R E f g a' b' h' hm := by
  apply moduleHomElement_ext R E
  intro x
  simp only [dgGluingModuleConeElement_π, map_add]
  exact dgGluingConeCochain_add _ _ _ _ _ _ _ _ hm

/-- 実 end 内の同じ三成分作用は係数環のスカラー倍を保存する。 -/
lemma dgGluingModuleConeElement_smul {M N P Q : ModuleCategory R E}
    (f : M ⟶ N) (g : P ⟶ Q) {n m : ℤ} (a) (b) (h) (hm : m + 1 = n) (r : R) :
    dgGluingModuleConeElement R E f g (r • a) (r • b) (r • h) hm =
      r • dgGluingModuleConeElement R E f g a b h hm := by
  apply moduleHomElement_ext R E
  intro x
  simp only [dgGluingModuleConeElement_π, map_smul]
  exact dgGluingConeCochain_smul _ _ _ _ _ hm r

/-- 比較差を含む微分式は、対象別 cochain だけでなく実 end 内で成り立つ。 -/
lemma dgGluingModuleConeElement_differential {M N P Q : ModuleCategory R E}
    (f : M ⟶ N) (g : P ⟶ Q) {n m : ℤ} (a) (b) (h) (hm : m + 1 = n) :
    (moduleHom R E (ForgetEnrichment.to (Complex R) (moduleCone R E f))
      (ForgetEnrichment.to (Complex R) (moduleCone R E g))).d n (n + 1)
        (dgGluingModuleConeElement R E f g a b h hm) =
      dgGluingModuleConeElement R E f g
        ((moduleHom R E (ForgetEnrichment.to (Complex R) M)
          (ForgetEnrichment.to (Complex R) P)).d n (n + 1) a)
        ((moduleHom R E (ForgetEnrichment.to (Complex R) N)
          (ForgetEnrichment.to (Complex R) Q)).d n (n + 1) b)
        (compose R (x := ForgetEnrichment.to (Complex R) M)
            (y := ForgetEnrichment.to (Complex R) P)
            (z := ForgetEnrichment.to (Complex R) Q)
            (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) g)).val a (add_zero n) -
          compose R (x := ForgetEnrichment.to (Complex R) M)
            (y := ForgetEnrichment.to (Complex R) N)
            (z := ForgetEnrichment.to (Complex R) Q)
            b (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val (zero_add n) -
          (moduleHom R E (ForgetEnrichment.to (Complex R) M)
            (ForgetEnrichment.to (Complex R) Q)).d m n h) rfl := by
  apply moduleHomElement_ext R E
  intro x
  simp only [moduleHomElement_d_π, dgGluingModuleConeElement_π, map_sub,
    moduleHomCompose_π, ← moduleEvaluation_cochain]
  exact dgGluingConeCochain_differential _ _ _ _ _ hm

end SerrePositivity.KST.SConstruction
