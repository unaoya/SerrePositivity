module

public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectCartesianScalarComparison
public import SerrePositivity.AlgebraicGeometry.ProjectivePerfectAffineCechComparison
public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechSquareAffineComparison

/-!
概要：同じ F8 の既知の完全性を、任意の有限アフィン被覆の native な四角形へ移す。
方針：実際の閉中心のアフィン性・分離性を供給し、同じ四角形の共通細分比較を使う。
規約：F8 の完全性や閉中心の被覆比較の条件を追加仮定にしない。
使われ方：一つの整合したアフィン被覆でのブローアップの降下の帰納。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (I : Ideal R)
variable {Y : Scheme.{u}} (iY : Y ⟶ Spec (CommRingCat.of (R ⧸ I ^ 1))) (g : Y ⟶ Proj G)
variable (H : IsPullback g iY (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))
  (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1)))))

include H in
/-- 実際の Cartesian な閉中心は、商の Spec の閉埋め込みの底変換。 -/
theorem projectivePerfectCartesianClosedImmersion : IsClosedImmersion g :=
  MorphismProperty.of_isPullback H.flip
    (IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ 1))) Ideal.Quotient.mk_surjective)

include H in
/-- 実際の閉中心は、分離的な Proj の閉部分スキームとして分離的。 -/
theorem projectivePerfectCartesianSeparated : Y.IsSeparated := by
  have : IsClosedImmersion g := projectivePerfectCartesianClosedImmersion G I iY g H
  refine ⟨?_⟩
  simpa only [terminal.comp_from] using
    (inferInstance : IsSeparated (g ≫ terminal.from (Proj G)))

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable [Surjective (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G))]

include hA hspan in
set_option backward.isDefEq.respectTransparency false in
/-- 同じ native な射影四角形の全複体は、任意の有限アフィン被覆で完全。
BST13 Lemma 3.9・BS17 Lemma 4.6(i) に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem projectivePerfectCartesianScalarSquare_acyclic
    {κ : Type} [LinearOrder κ] [Fintype κ] (V : κ → (Proj G).Opens)
    (hV : ∀ j, IsAffineOpen (V j)) (hcV : (⨆ j, V j) = ⊤) :
    (projectivePerfectCartesianScalarSquare G I iY g H p hp hR V).totalComplex.Acyclic := by
  have : IsClosedImmersion g := projectivePerfectCartesianClosedImmersion G I iY g H
  have : Y.IsSeparated := projectivePerfectCartesianSeparated G I iY g H
  exact (schemeStructurePerfectCechSquare_commonAffine_acyclic_iff
    g (Ideal.Quotient.mk (I ^ 1)) (projectiveScalarToGlobalSections G) (schemeScalarHom Y iY)
    (projectivePerfectCartesianScalarCompatibility G I iY g H)
    p hp hR (frobeniusQuotientPrimeCast p hR (I ^ 1))
    (projectiveProjPresheaf_primeCast G p hR) (projectivePullbackPresheaf_primeCast G g p hR)
    (projectiveProjCechOpen (ι := ι) G) V
    (projectivePerfectAffineCechOpen_isAffine G) hV
    (projectivePerfectAffineCechOpen_iSup G hspan) hcV).mp
      (projectivePerfectCartesianScalarSquare_standard_acyclic G I p hp hR hA hspan iY g H)

end SerrePositivity.AlgebraicGeometry
