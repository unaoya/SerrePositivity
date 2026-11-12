module

public import SerrePositivity.BhattScholze.Andre.Transfinite.Colimit
public import SerrePositivity.BhattScholze.Delta.Extension.DeltaPDCompletion
public import SerrePositivity.BhattScholze.Prism.Basic.Rigidity
public import SerrePositivity.BhattScholze.Prismatic.PrismOver
public import SerrePositivity.BhattScholze.Semiperfectoid.LciEnvelopeRegular
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PDCompletionResidue
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalCompletionUniformBound
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul

/-!
# 有界剰余を持つ実二元完備化の prism

## 概要
有界剰余による分母の正則性、標準 δ 構造と全 prism への一意延長を組み合わせる。
## 方針
既存の環・加群・実完備化の普遍性と有限段の一意性を使い、単位を保つ比較を構成する。
## 規約
BS 著者版 Proposition 7.10。生の余極限と実完備化を区別し、零環を含む。
## 使われ方
S′ の有界包絡、全有界試験 prism への始性と Corollary 7.3 の比較。
-/

/-! ## PDCompletionRegularBoundedQuotient -/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open CategoryTheory CategoryTheory.Limits DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (A : Type u) [CommRing A] (p : ℕ) (d : A)

/-- 概要：正則元の実二元完備化での像は、元の剰余の有界ねじれにより非零因子。
方針：p 完備化した d 錐を、離散な A/d の完備化の係数制限へ比較する。
規約：BS 著者版 Proposition 7.10。標的の p 正則性を追加しない。
使われ方：S′ の完備余極限の Cartier 条件。 -/
theorem pdCompletion_generator_regular_of_bounded_quotient
    (hd : IsSMulRegular A d)
    (hbound : ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ Ideal.span {d}),
      (p : A ⧸ Ideal.span {d}) ^n * x = 0 → (p : A ⧸ Ideal.span {d}) ^N * x = 0) :
    letI := pdCompletionCommRing A p d
    IsRegular (pdCompletionUnit A p d d) := by
  let Q := A ⧸ Ideal.span {d}
  let q := Ideal.Quotient.mk (Ideal.span {d})
  let X := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A A)
  let U := boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q Q)
  letI := q.toAlgebra
  have htor : scalarExtensionTorVanishing q (ModuleCat.of A A) := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
    exact isZero_Tor_succ_of_projective (ModuleCat A) (baseChangeScalarModule q) (ModuleCat.of A A) k
  let eM := (TensorProduct.AlgebraTensorModule.rid A Q Q).toModuleIso
  let eU : (boundedAboveDerivedBaseChange q).obj X ≅ U :=
    boundedAboveDerivedBaseChangeModuleAugmentationIso q (ModuleCat.of A A) htor ≪≫
      boundedAboveDerivedSingleFunctor.mapIso eM
  let e0 : (derivedScalarConeFunctor A d).obj X.obj ≅ (derivedRestrictScalars q).obj U.obj :=
    (restrictedDerivedQuotientKoszulIso d hd X).symm ≪≫
      DerivedCategory.Minus.ι.mapIso ((boundedAboveDerivedRestrictScalars q).mapIso eU)
  let V := (boundedAboveDerivedCompletionFunctor Q (q (p : A))).obj U
  have hb : ∃ N : ℕ, ∀ (n : ℕ) (x : Q),
      q (p : A) ^n * x = 0 → q (p : A) ^N * x = 0 := by
    simpa only [map_natCast] using hbound
  obtain ⟨hge, _, _⟩ := Andre.Transfinite.completedUnit_pure_bounded_torsion Q (q (p : A)) hb
  have hZ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q) (-1)).obj V.obj) := by
    letI := hge
    exact DerivedCategory.isZero_of_isGE _ 0 (-1) (by omega)
  have hZR : IsZero ((ModuleCat.restrictScalars q).obj
      ((DerivedCategory.homologyFunctor (ModuleCat Q) (-1)).obj V.obj)) := by
    have hs := ModuleCat.subsingleton_of_isZero hZ
    letI : Subsingleton ((ModuleCat.restrictScalars q).obj
      ((DerivedCategory.homologyFunctor (ModuleCat Q) (-1)).obj V.obj)) := hs
    exact ModuleCat.isZero_of_subsingleton _
  have hZR' := hZR.of_iso ((derivedRestrictScalarsHomologyIso q (-1)).app V.obj)
  let e := (derivedComplexCompletionFunctor A (p : A)).mapIso e0 ≪≫
    (derivedCompletionRestrictionIso q (p : A)).app U.obj
  apply pdCompletion_generator_regular_of_completed_scalarCone_homology_isZero A p d
  exact hZR'.of_iso ((DerivedCategory.homologyFunctor (ModuleCat A) (-1)).mapIso e)

end SerrePositivity.BhattScholze

end

/-! ## PDCompletionPrismExtension -/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open DerivedCompletion
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]

/-- 概要：distinguished 元をイデアルに送る δ 射は実 (p,d) 完備化へ一意に延長。
方針：像の元は標的の選択生成元の単元倍であり、標的の主元完備性を移せる。
規約：BS 著者版 Lemma 3.5・Proposition 7.10。全 prism が標的。
使われ方：S′ の全有界試験 prism への一意な射。 -/
theorem existsUnique_pdCompletionPrismExtension (D : DeltaStructure p A) (d : A)
    (hd : D.IsDistinguished d) (Y : OrientedPrism p B)
    (f : A →+* B) (hf : D.IsDeltaHom Y.deltaStructure f) (hfd : f d ∈ Y.ideal) :
    letI := pdCompletionCommRing A p d
    ∃! g : PDCompletionH0 A p d →+* B,
      (deltaPDCompletionStructure D d).IsDeltaHom Y.deltaStructure g ∧
        g.comp (pdCompletionUnit A p d) = f := by
  obtain ⟨r, hr, he⟩ := hf.exists_isUnit_of_distinguished_of_mem_span hd hfd
    Y.generator_mem_jacobson Y.p_mem_jacobson
  have hI : Ideal.span {f d} = Y.ideal := by
    rw [he, Ideal.span_singleton_mul_right_unit hr]
    rfl
  have hcomplete : IsModuleComplete B (f d) (ModuleCat.of B B) := by
    letI : IsAdicComplete (Ideal.span {f d}) B := by
      rw [hI]
      exact Y.isAdicComplete_generator
    exact isModuleComplete_of_isAdicComplete B (f d) (ModuleCat.of B B)
  exact existsUnique_deltaPDCompletionHom D d Y.deltaStructure f hf Y.complete_p hcomplete

end SerrePositivity.BhattScholze

end

/-! ## BoundedPDCompletion -/

public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
open DerivedCompletion CategoryTheory
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 概要：実 (p,d) 完備化で d が正則、元の d 剰余が有界なら有界 prism が得られる。
方針：distinguished 性と完備性で prism を作り、実剰余比較で有界ねじれを移す。
規約：BS 著者版 Proposition 7.10。p 正則性は要求しない。
使われ方：S′ の完備包絡の有界性。 -/
theorem exists_boundedPrism_on_pdCompletion (D : DeltaStructure p A) (d : A)
    (hd : D.IsDistinguished d)
    (hreg : letI := pdCompletionCommRing A p d
      Function.Injective (fun x : PDCompletionH0 A p d => pdCompletionUnit A p d d * x))
    (hbound : ∃ N : ℕ, ∀ (n : ℕ) (x : A ⧸ Ideal.span {d}),
      (p : A ⧸ Ideal.span {d}) ^n * x = 0 → (p : A ⧸ Ideal.span {d}) ^N * x = 0) :
    letI := pdCompletionCommRing A p d
    ∃ Q : OrientedPrism p (PDCompletionH0 A p d),
      Q.deltaStructure = deltaPDCompletionStructure D d ∧
        Q.generator = pdCompletionUnit A p d d ∧ Prismatic.IsBoundedPrism Q := by
  letI := pdCompletionCommRing A p d
  let B := PDCompletionH0 A p d
  let j := pdCompletionUnit A p d
  letI : Algebra A B := j.toAlgebra
  letI : Module A B := Algebra.toModule
  have hp : IsModuleComplete B (p : B) (ModuleCat.of B B) := by
    have h := (isModuleComplete_algebraMap_iff A B (p : A) B).mpr (pdCompletionH0_isComplete_p A p d)
    simpa only [map_natCast] using h
  have hdc : IsModuleComplete B (j d) (ModuleCat.of B B) :=
    (isModuleComplete_algebraMap_iff A B d B).mpr (pdCompletionH0_isComplete_d A p d)
  let Q := OrientedPrism.ofDistinguished (deltaPDCompletionStructure D d) (j d)
    ((pdCompletionUnit_isDeltaHom D d).map_isDistinguished hd) hreg hp hdc
  refine ⟨Q, rfl, rfl, ?_⟩
  change ∃ N : ℕ, ∀ (n : ℕ) (x : B ⧸ Ideal.span {j d}),
    (p : B ⧸ Ideal.span {j d}) ^n * x = 0 → (p : B ⧸ Ideal.span {j d}) ^N * x = 0
  let S := A ⧸ Ideal.span {d}
  letI := principalCompletionCommRing S (p : S)
  let e := pdCompletionResidueEquiv A p d
  obtain ⟨N, hN⟩ := hbound
  have h := principalCompletionH0_uniform_torsion_bound S (p : S) N hN
  have hjp : principalCompletionUnitRingHom S (p : S) (p : S) = (p : PrincipalCompletionH0 S (p : S)) :=
    map_natCast (principalCompletionUnitRingHom S (p : S)) p
  refine ⟨N, fun n x hx => ?_⟩
  apply e.injective
  have hx' : (p : PrincipalCompletionH0 S (p : S)) ^n * e x = 0 := by
    simpa only [map_mul, map_pow, map_natCast, map_zero] using congrArg e hx
  have h' := h n (e x) (by simpa only [hjp] using hx')
  simpa only [map_mul, map_pow, map_natCast, map_zero, hjp] using h'

end SerrePositivity.BhattScholze

end
