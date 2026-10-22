module
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeDifferential

/-! # 実加群 Hom 内の三成分 cone 作用の合成
概要：比較ホモトピーを含む合成式を実 end 内で証明する。
方針：元の Hom 評価と通常順合成を保って cochain 合成式へ帰着する。
規約：左右次数の符号を保持。使われ方：実 dg cone 関手の合成保存。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]

/-- 同じ end 内の三成分作用は、第三成分の符号を保持する斉次合成式を満たす。 -/
lemma dgGluingModuleConeElement_comp {M N P Q T U : ModuleCategory R E}
    (f : M ⟶ N) (g : P ⟶ Q) (j : T ⟶ U) {n m p l : ℤ}
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
      (ForgetEnrichment.to (Complex R) U)).X l) (hl : l + 1 = p) :
    compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R E f))
        (y := ForgetEnrichment.to (Complex R) (moduleCone R E g))
        (z := ForgetEnrichment.to (Complex R) (moduleCone R E j))
        (dgGluingModuleConeElement R E g j c d k hl)
        (dgGluingModuleConeElement R E f g a b h hm) rfl =
      dgGluingModuleConeElement R E f j (n := n + p) (m := m + p)
        (compose R (x := ForgetEnrichment.to (Complex R) M)
          (y := ForgetEnrichment.to (Complex R) P)
          (z := ForgetEnrichment.to (Complex R) T) c a rfl)
        (compose R (x := ForgetEnrichment.to (Complex R) N)
          (y := ForgetEnrichment.to (Complex R) Q)
          (z := ForgetEnrichment.to (Complex R) U) d b rfl)
        (compose R (x := ForgetEnrichment.to (Complex R) M)
            (y := ForgetEnrichment.to (Complex R) P)
            (z := ForgetEnrichment.to (Complex R) U) k a (by omega : n + l = m + p) +
          p.negOnePow • compose R (x := ForgetEnrichment.to (Complex R) M)
            (y := ForgetEnrichment.to (Complex R) Q)
            (z := ForgetEnrichment.to (Complex R) U) d h rfl) (by omega) := by
  apply moduleHomElement_ext R E
  intro x
  simp only [moduleHomCompose_π, dgGluingModuleConeElement_π, map_add,
    Units.smul_def, map_zsmul]
  exact dgGluingConeCochain_comp _ _ _ _ _ _ hm _ _ _ hl

end SerrePositivity.KST.SConstruction
