module
public import SerrePositivity.KST.SConstruction.DGConeDescCochainNaturality
public import SerrePositivity.DifferentialGraded.Module.ConeConstruction

/-!
概要：指定 cone descent の全次数自然性を実加群 Hom end 上に持ち上げる。
方針：元加群対象を固定してから各評価で二成分の cochain 等号を使う。
規約：微分境界と独立に同じ元斉次比較を保持する。
使われ方：実 cone 比較の全関手族化における小さい計算入口。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex CochainComplex HomComplex
open DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 概要：元 descent の左右入力の全自然性は同じ実 Hom end の全自然性を与える。
方針：元固定対象における実 cochain 二成分の照合を各評価へ適用する。
規約：次数零への制限をしない。使われ方：指定ホモトピーを持つ実比較の自然性。 -/
lemma dgConeDescModule_naturality {M N M' N' T T' : ModuleCategory R D}
    (f : M ⟶ N) (g : M' ⟶ N') {n : ℤ}
    (a : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) M')).X n)
    (b : (moduleHom R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) N')).X n)
    (c : (moduleHom R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) T')).X n)
    (h : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) T)).X (-1))
    (h' : (moduleHom R D (ForgetEnrichment.to (Complex R) M')
      (ForgetEnrichment.to (Complex R) T')).X (-1))
    (q : N ⟶ T) (q' : N' ⟶ T')
    (hh : compose R (x := ForgetEnrichment.to (Complex R) M)
      (y := ForgetEnrichment.to (Complex R) T) (z := ForgetEnrichment.to (Complex R) T')
      c h (by omega : -1 + n = n - 1) = n.negOnePow •
      compose R (x := ForgetEnrichment.to (Complex R) M)
        (y := ForgetEnrichment.to (Complex R) M') (z := ForgetEnrichment.to (Complex R) T')
        h' a (by omega : n + -1 = n - 1))
    (hq : compose R (x := ForgetEnrichment.to (Complex R) N)
      (y := ForgetEnrichment.to (Complex R) N') (z := ForgetEnrichment.to (Complex R) T')
      (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) q')).val b (add_zero n) =
      compose R (x := ForgetEnrichment.to (Complex R) N)
        (y := ForgetEnrichment.to (Complex R) T) (z := ForgetEnrichment.to (Complex R) T')
        c (cycleFromUnit _ (ForgetEnrichment.homTo (Complex R) q)).val (zero_add n)) :
    compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R D f))
      (y := ForgetEnrichment.to (Complex R) (moduleCone R D g))
      (z := ForgetEnrichment.to (Complex R) T')
      (moduleConeDescElement R D g h' q')
      (dgGluingModuleConeElement R D f g a b
        (0 : (moduleHom R D (ForgetEnrichment.to (Complex R) M)
          (ForgetEnrichment.to (Complex R) N')).X (n - 1)) (by omega)) (add_zero n) =
    compose R (x := ForgetEnrichment.to (Complex R) (moduleCone R D f))
      (y := ForgetEnrichment.to (Complex R) T) (z := ForgetEnrichment.to (Complex R) T')
      c (moduleConeDescElement R D f h q) (zero_add n) := by
  apply moduleHomElement_ext R D
  intro e
  have hh' := congrArg ((moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) T') e).f (n - 1)) hh
  rw [moduleHomCompose_π, Units.smul_def, map_zsmul, moduleHomCompose_π] at hh'
  have hq' := congrArg ((moduleHomπ R D (ForgetEnrichment.to (Complex R) N)
    (ForgetEnrichment.to (Complex R) T') e).f n) hq
  rw [moduleHomCompose_π, moduleHomCompose_π] at hq'
  rw [moduleHomCompose_π, moduleConeDescElement_π, dgGluingModuleConeElement_π,
    moduleHomCompose_π, moduleConeDescElement_π, map_zero]
  rw [← moduleEvaluation_cochain, ← moduleEvaluation_cochain] at hq'
  let qe := Cochain.ofHom ((moduleEvaluation R D e).map q)
  let qe' := Cochain.ofHom ((moduleEvaluation R D e).map q')
  let he := (moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
    (ForgetEnrichment.to (Complex R) T) e).f (-1) h
  let he' := (moduleHomπ R D (ForgetEnrichment.to (Complex R) M')
    (ForgetEnrichment.to (Complex R) T') e).f (-1) h'
  have hc := dgConeDescCochain_naturality ((moduleEvaluation R D e).map f)
    ((moduleEvaluation R D e).map g)
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) M)
      (ForgetEnrichment.to (Complex R) M') e).f n a)
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) N)
      (ForgetEnrichment.to (Complex R) N') e).f n b)
    ((moduleHomπ R D (ForgetEnrichment.to (Complex R) T)
      (ForgetEnrichment.to (Complex R) T') e).f n c) he he' qe qe' hh' hq'
  exact (congrArg (fun t => t.comp
      (mappingCone.descCochain ((moduleEvaluation R D e).map g) he' qe' (by omega))
      (add_zero n))
    (dgGluingConeCochain_zero_comparison ((moduleEvaluation R D e).map f)
      ((moduleEvaluation R D e).map g) _ _ (by omega : (n - 1) + 1 = n))).trans hc

end SerrePositivity.KST.SConstruction
