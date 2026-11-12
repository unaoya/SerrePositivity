module
public import SerrePositivity.KST.SConstruction.DGModuleConeInputIsoNaturality

/-!
概要：同じ入力同型の元 cone 作用を二つの実族の斉次作用へ接続する。
方針：元実作用の二回収式を入力同型の自然性へ代入する。
規約：元二つの入力同型と全整数次数を保持する。
使われ方：具体的 gluing cone 族の全自然性の型照合。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：同じ実作用を回収する二族は元入力 cone 同型で全次数可換。
方針：元二つの作用回収を同じ入力同型の自然性へ代入する。
規約：元作用・元入力等号を保持。使われ方：元 gluing cone 全入力比較。 -/
lemma dgModuleConeInputIso_family_naturality {M N M' N' : ModuleCategory R D}
    (f f' : M ⟶ N) (g g' : M' ⟶ N') (ef : f = f') (eg : g = g')
    (e : moduleCone R D f ≅ moduleCone R D f')
    (e' : moduleCone R D g ≅ moduleCone R D g')
    (he : e = eqToIso (congrArg (fun t => moduleCone R D t) ef))
    (he' : e' = eqToIso (congrArg (fun t => moduleCone R D t) eg))
    (n : ℤ)
    (a : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) M')).X n)
    (b : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) N')).X n)
    (s : (moduleHom R D (ForgetEnrichment.to (Complex R) (moduleCone R D f))
      (ForgetEnrichment.to (Complex R) (moduleCone R D g))).X n)
    (t : (moduleHom R D (ForgetEnrichment.to (Complex R) (moduleCone R D f'))
      (ForgetEnrichment.to (Complex R) (moduleCone R D g'))).X n)
    (hs : s = dgGluingModuleConeElement R D f g a b 0 (sub_add_cancel n 1))
    (ht : t = dgGluingModuleConeElement R D f' g' a b 0 (sub_add_cancel n 1)) :
    compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R D f))
      (y := ForgetEnrichment.to (Complex R) (moduleCone R D g))
      (z := ForgetEnrichment.to (Complex R) (moduleCone R D g'))
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) e'.hom)).val s (add_zero n) =
    compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R D f))
      (y := ForgetEnrichment.to (Complex R) (moduleCone R D f'))
      (z := ForgetEnrichment.to (Complex R) (moduleCone R D g')) t
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) e.hom)).val (zero_add n) := by
  rw [he, he', hs, ht]
  exact dgModuleConeInputIso_naturality R D f f' g g' ef eg n a b
end SerrePositivity.KST.SConstruction
