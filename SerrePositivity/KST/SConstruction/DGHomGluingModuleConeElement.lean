module
public import SerrePositivity.KST.SConstruction.DGHomGluingConeComposition
public import SerrePositivity.DifferentialGraded.Module.ConeHomotopyDesc

/-! # 三成分 cone 作用の実加群 Hom 元
概要：左右の斉次自然変換と第三成分から、実 end 内の cone 間の元を作る。
方針：元の cone の四つの加群 Hom 元を合成し、評価で同じ cochain 式を回収する。
規約：対象別 cochain の族から自然性を仮定しない。使われ方：全 Hom の dg cone 関手。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]

/-- 三成分作用を元の加群 Hom の end 内で構成した実斉次元。 -/
def dgGluingModuleConeElement {M N P Q : ModuleCategory R E}
    (f : M ⟶ N) (g : P ⟶ Q) {n m : ℤ}
    (a : (moduleHom R E (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) P)).X n)
    (b : (moduleHom R E (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) Q)).X n)
    (h : (moduleHom R E (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) Q)).X m) (hm : m + 1 = n) :
    (moduleHom R E (ForgetEnrichment.to (Complex R) (moduleCone R E f))
      (ForgetEnrichment.to (Complex R) (moduleCone R E g))).X n :=
  n.negOnePow •
    compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R E f))
      (y := ForgetEnrichment.to (Complex R) P)
      (z := ForgetEnrichment.to (Complex R) (moduleCone R E g))
      (moduleConeInlElement R E g)
      (compose R a (moduleConeFstElement R E f) (by omega : 1 + n = n + 1))
      (by omega) +
    compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R E f))
      (y := ForgetEnrichment.to (Complex R) Q)
      (z := ForgetEnrichment.to (Complex R) (moduleCone R E g))
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (moduleConeInr R E g))).val
      (compose R b (moduleConeSndElement R E f) (zero_add n)) (add_zero n) -
    n.negOnePow •
      compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R E f))
        (y := ForgetEnrichment.to (Complex R) Q)
        (z := ForgetEnrichment.to (Complex R) (moduleCone R E g))
        (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) (moduleConeInr R E g))).val
        (compose R h (moduleConeFstElement R E f) (by omega : 1 + m = n)) (add_zero n)

/-- 実 end の評価は、比較ホモトピーを含む元の三成分 cochain そのもの。 -/
lemma dgGluingModuleConeElement_π {M N P Q : ModuleCategory R E}
    (f : M ⟶ N) (g : P ⟶ Q) {n m : ℤ} (a) (b) (h) (hm : m + 1 = n) (x : E) :
    (moduleHomπ R E (ForgetEnrichment.to (Complex R) (moduleCone R E f))
      (ForgetEnrichment.to (Complex R) (moduleCone R E g)) x).f n
        (dgGluingModuleConeElement R E f g a b h hm) =
      dgGluingConeCochain ((moduleEvaluation R E x).map f)
        ((moduleEvaluation R E x).map g)
        ((moduleHomπ R E (ForgetEnrichment.to (Complex R) M)
          (ForgetEnrichment.to (Complex R) P) x).f n a)
        ((moduleHomπ R E (ForgetEnrichment.to (Complex R) N)
          (ForgetEnrichment.to (Complex R) Q) x).f n b)
        ((moduleHomπ R E (ForgetEnrichment.to (Complex R) M)
          (ForgetEnrichment.to (Complex R) Q) x).f m h) hm := by
  unfold dgGluingModuleConeElement
  simp only [Units.smul_def, map_sub, map_add, map_zsmul, moduleHomCompose_π,
    moduleConeInlElement_π, moduleConeFstElement_π, moduleConeSndElement_π,
    ← moduleEvaluation_cochain, moduleConeInr_eval]
  simp only [dgGluingConeCochain, mappingCone.liftCochain,
    Cochain.sub_comp, Units.smul_def, Cochain.smul_comp]
  abel

end SerrePositivity.KST.SConstruction
