module

public import SerrePositivity.AlgebraicGeometry.ProjectiveFrobeniusCanonicalDiagram
public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitModuleIso
public import SerrePositivity.AlgebraicGeometry.ProjectiveProjCechComplexIso
public import SerrePositivity.AlgebraicGeometry.OpenCoverFrobeniusRefinement

/-!
概要：F8 の実際の斉次局所化の Frobenius 係数を、Proj の実際の構造層へ移す。
方針：非空交叉の環の同型とその自然性を Frobenius 順極限へ送り、全タプル複体にする。
規約：空交叉の斉次局所化と大域切断を同一視しない。
使われ方：共通アフィン比較を F8 の固定した標準開の複体に接続する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry TopologicalSpace Opposite
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 非空の標準開交叉の環の同型。2e の切断の同型と同じ写像を使う。 -/
def projectiveProjCechSectionRingIso (T : Finset ι) (hT : T.Nonempty) :
    CommRingCat.of (HomogeneousLocalization.Away G
      (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T))) ≅
        (Proj G).presheaf.obj (op (cechOpenIntersection (projectiveProjCechOpen G) T)) :=
  projectiveProjStandardSectionIso G T hT ≪≫
    (Proj G).presheaf.mapIso (eqToIso (congrArg op (projectiveProjCechOpen_intersection G T)))

/-- 環の切断の同型は、2e の同じ非空交叉の制限と可換。 -/
theorem projectiveProjCechSectionRingIso_naturality {T U : Finset ι}
    (hT : T.Nonempty) (h : T ⊆ U) (x : (projectiveHomogeneousChartDiagram G).obj T) :
    (projectiveProjCechSectionRingIso G U (hT.mono h)).hom.hom
        (((algebraCechRingDiagram (projectiveHomogeneousChartAlgebraDiagram G)).map
          (homOfLE h)).hom x) =
      ((Proj G).presheaf.map
        (homOfLE (cechOpenIntersection_antitone (projectiveProjCechOpen G) h)).op).hom
        ((projectiveProjCechSectionRingIso G T hT).hom.hom x) :=
  congrArg (fun m ↦ m.hom x) (projectiveProjCechSectionLinearEquiv_naturality G hT h)

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

include hR in
/-- 基底の p の零化は、実際の Proj の全ての開集合の切断環で成り立つ。 -/
theorem projectiveProjPresheaf_primeCast (O : (Proj G).Opensᵒᵖ) :
    (p : (Proj G).presheaf.obj O) = 0 := by
  let f := ((Proj G).presheaf.map (homOfLE (show O.unop ≤ ⊤ from le_top)).op).hom.comp
    (projectiveScalarToGlobalSections G)
  simpa only [map_natCast, map_zero] using congrArg f hR

/-- 非空交叉で、実際の環の Frobenius 順極限の係数を同定する。 -/
def projectivePerfectNativeCechCoefficientIso (T : Finset ι) (hT : T.Nonempty) :
    (projectiveHomogeneousPerfectChartDiagram (ι := ι) G p hp hR).obj T ≅
      (openCoverCechDiagram
        (frobeniusRingDiagram (Proj G).presheaf p hp (projectiveProjPresheaf_primeCast G p hR))
        (projectiveProjCechOpen (ι := ι) G)).obj T :=
  frobeniusDirectLimitModuleIso p hp (projectiveHomogeneousChart_primeCast G p hR T)
    (projectiveProjPresheaf_primeCast G p hR _) (projectiveProjCechSectionRingIso G T hT)

/-- 非空交叉の同型は、Frobenius 順極限後も同じ実際の制限写像と可換。 -/
theorem projectivePerfectNativeCechCoefficientIso_naturality {T U : Finset ι}
    (hT : T.Nonempty) (h : T ⊆ U) :
    (projectiveHomogeneousPerfectChartDiagram (ι := ι) G p hp hR).map (homOfLE h) ≫
        (projectivePerfectNativeCechCoefficientIso G p hp hR U (hT.mono h)).hom =
      (projectivePerfectNativeCechCoefficientIso G p hp hR T hT).hom ≫
        (openCoverCechDiagram
          (frobeniusRingDiagram (Proj G).presheaf p hp (projectiveProjPresheaf_primeCast G p hR))
          (projectiveProjCechOpen (ι := ι) G)).map (homOfLE h) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change FrobeniusDirectLimit (HomogeneousLocalization.Away G
    (algebraMap (MvPolynomial ι R) A (projectiveLaurentDenominator R T))) p hp
      (projectiveHomogeneousChart_primeCast G p hR T) at x
  obtain ⟨n, x, rfl⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap _ p hp (projectiveHomogeneousChart_primeCast G p hR T)) x
  change frobeniusDirectLimitOf _ p hp _ n
      ((projectiveProjCechSectionRingIso G U (hT.mono h)).hom.hom
        (((algebraCechRingDiagram (projectiveHomogeneousChartAlgebraDiagram G)).map
          (homOfLE h)).hom x)) =
    frobeniusDirectLimitOf _ p hp _ n
      (((Proj G).presheaf.map
        (homOfLE (cechOpenIntersection_antitone (projectiveProjCechOpen G) h)).op).hom
        ((projectiveProjCechSectionRingIso G T hT).hom.hom x))
  exact congrArg (frobeniusDirectLimitOf _ p hp _ n)
    (projectiveProjCechSectionRingIso_naturality G hT h x)

/-- F8 の固定した複体と、実際の Proj の構造層の Frobenius 係数の Čech 複体の同型。
BST13 Lemma 3.9 と Stacks 30.2.6 の標準開計算に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
def projectivePerfectNativeCechComplexIso :
    fullCechComplex (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA) ≅
      fullCechComplex (openCoverCechDiagram
        (frobeniusRingDiagram (Proj G).presheaf p hp (projectiveProjPresheaf_primeCast G p hR))
        (projectiveProjCechOpen (ι := ι) G)) :=
  fullCechComplexFunctor.mapIso (projectiveFrobeniusRingChartDiagram_isoCanonical G p hp hR hA) ≪≫
    fullCechNonemptyComplexIso (projectivePerfectNativeCechCoefficientIso G p hp hR)
      (fun hT h ↦ projectivePerfectNativeCechCoefficientIso_naturality G p hp hR hT h)

/-- 複体の比較は各タプルで、同じ非空交叉の環の順極限の同型を適用する。 -/
theorem projectivePerfectNativeCechComplexIso_apply (q : ℕ)
    (a : (fullCechComplex
      (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)).X q)
    (t : Fin (q + 1) → ι) :
    (((projectivePerfectNativeCechComplexIso (ι := ι) G p hp hR hA).hom.f q).hom a) t =
      (projectivePerfectNativeCechCoefficientIso G p hp hR (cechTupleSupport t)
        (cechTupleSupport_nonempty t)).hom.hom (a t) := rfl

end SerrePositivity.AlgebraicGeometry
