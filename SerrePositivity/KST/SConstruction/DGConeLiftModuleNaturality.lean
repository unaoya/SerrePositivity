module
public import SerrePositivity.KST.SConstruction.DGConeLiftCochainNaturality
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-!
概要：元二成分からの cone lift の全自然性を実加群 Hom end へ持ち上げる。
方針：元加群対象を固定し、同じ cochain の二射影検出を各評価へ適用する。
規約：次数一成分の符号を保持。使われ方：実回転比較の全厳密自然性。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：指定二成分の全自然性は同じ実 cone lift の全自然性を与える。
方針：実 Hom end の各評価で同じ二射影計算を使う。
規約：元斉次元と全整数次数を保持。使われ方：全厳密回転比較の入力計算。 -/
lemma dgConeLiftModule_naturality {M N M' N' T T' : ModuleCategory R D}
    (f : M ⟶ N) (g : M' ⟶ N') {n : ℤ}
    (a : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) M')).X n)
    (b : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) N')).X n)
    (c : (moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) T')).X n)
    (h : (moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) M)).X 1)
    (h' : (moduleHom R D (ForgetEnrichment.to (Complex R) T')
      (ForgetEnrichment.to (Complex R) M')).X 1)
    (q : (moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) N)).X 0)
    (q' : (moduleHom R D (ForgetEnrichment.to (Complex R) T')
      (ForgetEnrichment.to (Complex R) N')).X 0)
    (hh : compose R (x := ForgetEnrichment.to (Complex R) T)
      (y := ForgetEnrichment.to (Complex R) M) (z := ForgetEnrichment.to (Complex R) M')
      a h (add_comm 1 n) = n.negOnePow •
      compose R (x := ForgetEnrichment.to (Complex R) T)
        (y := ForgetEnrichment.to (Complex R) T') (z := ForgetEnrichment.to (Complex R) M')
        h' c rfl)
    (hq : compose R (x := ForgetEnrichment.to (Complex R) T)
      (y := ForgetEnrichment.to (Complex R) N) (z := ForgetEnrichment.to (Complex R) N')
      b q (zero_add n) =
      compose R (x := ForgetEnrichment.to (Complex R) T)
        (y := ForgetEnrichment.to (Complex R) T') (z := ForgetEnrichment.to (Complex R) N')
        q' c (add_zero n)) :
    compose R (x := ForgetEnrichment.to (Complex R) T)
      (y := ForgetEnrichment.to (Complex R) (moduleCone R D f))
      (z := ForgetEnrichment.to (Complex R) (moduleCone R D g))
      (dgGluingModuleConeElement R D f g a b
        (0 : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
          (ForgetEnrichment.to (Complex R) N')).X (n - 1)) (by omega))
      (moduleConeLiftElement R D f 0 h q) (zero_add n) =
    compose R (x := ForgetEnrichment.to (Complex R) T)
      (y := ForgetEnrichment.to (Complex R) T')
      (z := ForgetEnrichment.to (Complex R) (moduleCone R D g))
      (moduleConeLiftElement R D g 0 h' q') c (add_zero n) := by
  apply moduleHomElement_ext R D
  intro e
  have hh' := congrArg ((moduleHomπ R D (ForgetEnrichment.to (Complex R) T)
    (ForgetEnrichment.to (Complex R) M') e).f (n + 1)) hh
  rw [moduleHomCompose_π, Units.smul_def, map_zsmul, moduleHomCompose_π] at hh'
  have hq' := congrArg ((moduleHomπ R D (ForgetEnrichment.to (Complex R) T)
    (ForgetEnrichment.to (Complex R) N') e).f n) hq
  rw [moduleHomCompose_π, moduleHomCompose_π] at hq'
  rw [moduleHomCompose_π, moduleConeLiftElement_π, dgGluingModuleConeElement_π,
    moduleHomCompose_π, moduleConeLiftElement_π, map_zero]
  have hc := dgConeLiftCochain_naturality ((moduleEvaluation R D e).map f)
    ((moduleEvaluation R D e).map g)
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) M') e).f n a)
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) N') e).f n b)
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) T') e).f n c)
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) M) e).f 1 h)
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) T')
      (ForgetEnrichment.to (Complex R) M') e).f 1 h')
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) N) e).f 0 q)
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) T')
      (ForgetEnrichment.to (Complex R) N') e).f 0 q') hh' hq'
  exact (congrArg (fun t => (mappingCone.liftCochain _
      ((moduleHomπ R D (ForgetEnrichment.to (Complex R) T)
        (ForgetEnrichment.to (Complex R) M) e).f 1 h)
      ((moduleHomπ R D (ForgetEnrichment.to (Complex R) T)
        (ForgetEnrichment.to (Complex R) N) e).f 0 q) rfl).comp t (zero_add n))
    (dgGluingConeCochain_zero_comparison ((moduleEvaluation R D e).map f)
      ((moduleEvaluation R D e).map g) _ _ (by omega : (n - 1) + 1 = n))).trans hc
end SerrePositivity.KST.SConstruction
