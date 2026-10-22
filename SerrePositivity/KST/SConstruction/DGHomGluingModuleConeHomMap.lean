module
public import SerrePositivity.KST.SConstruction.DGHomGluingModuleConeDifferential

/-! # 三成分の実 Hom 鎖写像の構成子
概要：二つの実鎖写像と比較 cochain から、元の二つの加群 cone の Hom 鎖写像を作る。
方針：三成分の線形性と比較差を持つ微分式を使う。
規約：比較 cochain の全次数境界式を明示する。使われ方：元の gluing Hom の特殊化。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {K : Complex R} {M N P Q : ModuleCategory R E} (f : M ⟶ N) (g : P ⟶ Q)
  (A : K ⟶ moduleHom R E (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) P))
  (B : K ⟶ moduleHom R E (ForgetEnrichment.to (Complex R) N)
    (ForgetEnrichment.to (Complex R) Q))
  (H : Cochain K (moduleHom R E (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) Q)) (-1))

private lemma coneElement_v_eq {i n m l : ℤ}
    (a : (moduleHom R E (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) P)).X n)
    (b : (moduleHom R E (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) Q)).X n) (z : K.X i)
    (hm : i + (-1) = m) (hl : i + (-1) = l)
    (hn : m + 1 = n) (hn' : l + 1 = n) :
    dgGluingModuleConeElement R E f g a b (H.v i m hm z) hn =
      dgGluingModuleConeElement R E f g a b (H.v i l hl z) hn' := by
  have he : m = l := by omega
  cases he
  rfl

/-- 三成分からの各次数の実線形作用。 -/
def dgGluingModuleConeLinear (n : ℤ) : K.X n ⟶
    (moduleHom R E (ForgetEnrichment.to (Complex R) (moduleCone R E f))
      (ForgetEnrichment.to (Complex R) (moduleCone R E g))).X n :=
  ModuleCat.ofHom {
    toFun := fun a => dgGluingModuleConeElement R E f g (A.f n a) (B.f n a)
      (H.v n (n - 1) (by omega) a) (by omega)
    map_add' := fun a b => by
      erw [map_add, map_add, map_add]
      exact dgGluingModuleConeElement_add R E f g (n := n) (m := n - 1)
        (A.f n a) (A.f n b) (B.f n a) (B.f n b)
        (H.v n (n - 1) (by omega) a) (H.v n (n - 1) (by omega) b) (by omega)
    map_smul' := fun r a => by
      erw [map_smul, map_smul, map_smul]
      exact dgGluingModuleConeElement_smul R E f g (n := n) (m := n - 1)
        (A.f n a) (B.f n a) (H.v n (n - 1) (by omega) a) (by omega) r }

variable (hH : ∀ (n : ℤ) (a : K.X n),
  H.v (n + 1) n (by omega) (K.d n (n + 1) a) =
    compose R (x := ForgetEnrichment.to (Complex R) M)
      (y := ForgetEnrichment.to (Complex R) P) (z := ForgetEnrichment.to (Complex R) Q)
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) g)).val (A.f n a) (add_zero n) -
    compose R (x := ForgetEnrichment.to (Complex R) M)
      (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) Q)
      (B.f n a) (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) f)).val (zero_add n) -
    (moduleHom R E (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) Q)).d (n - 1) n
      (H.v n (n - 1) (by omega) a))

include hH in
/-- 実線形作用は、元の比較差を持つ微分を保つ。 -/
lemma dgGluingModuleConeLinear_comm (n : ℤ) (a : K.X n) :
    (moduleHom R E (ForgetEnrichment.to (Complex R) (moduleCone R E f))
      (ForgetEnrichment.to (Complex R) (moduleCone R E g))).d n (n + 1)
        (dgGluingModuleConeLinear R E f g A B H n a) =
      dgGluingModuleConeLinear R E f g A B H (n + 1) (K.d n (n + 1) a) := by
  change (moduleHom R E (ForgetEnrichment.to (Complex R) (moduleCone R E f))
      (ForgetEnrichment.to (Complex R) (moduleCone R E g))).d n (n + 1)
    (dgGluingModuleConeElement R E f g (A.f n a) (B.f n a)
      (H.v n (n - 1) (by omega) a) (by omega)) =
    dgGluingModuleConeElement R E f g (A.f (n + 1) (K.d n (n + 1) a))
      (B.f (n + 1) (K.d n (n + 1) a))
      (H.v (n + 1) (n + 1 - 1) (by omega) (K.d n (n + 1) a)) (by omega)
  rw [← coneElement_v_eq R E f g H
    (A.f (n + 1) (K.d n (n + 1) a)) (B.f (n + 1) (K.d n (n + 1) a))
    (K.d n (n + 1) a) (by omega : n + 1 + (-1) = n)
    (by omega : n + 1 + (-1) = n + 1 - 1) rfl (by omega)]
  rw [dgGluingModuleConeElement_differential]
  have ha := ConcreteCategory.congr_hom (A.comm n (n + 1)) a
  have hb := ConcreteCategory.congr_hom (B.comm n (n + 1)) a
  erw [← ha, ← hb, hH n a]
  rfl

/-- 比較 cochain の境界式から作る、実 cone Hom への鎖写像。 -/
def dgGluingModuleConeHomMap : K ⟶
    moduleHom R E (ForgetEnrichment.to (Complex R) (moduleCone R E f))
      (ForgetEnrichment.to (Complex R) (moduleCone R E g)) where
  f n := dgGluingModuleConeLinear R E f g A B H n
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    exact dgGluingModuleConeLinear_comm R E f g A B H hH i a

end SerrePositivity.KST.SConstruction
