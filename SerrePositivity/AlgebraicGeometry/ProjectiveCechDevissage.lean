module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechComplex
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFiniteness
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
概要：射影 Čech 複体の短完全列からコホモロジーの有限性を得る。
方針：狭義増加版の消滅次数を上限にして、短完全列の連結写像で降下帰納する。
規約：各対象に対し、有限性が分かっている複体からの短完全表示を与える。
使われ方：多項式環の捻りの有限性を、有限生成次数付き加群に移す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory

variable {R : Type*} [CommRing R] [IsNoetherianRing R]
variable {ι : Type*} [LinearOrder ι] [Finite ι] {Obj : Type*}

/--
概要：有限性が分かっている対象による短完全表示を繰り返せば、各対象の射影 Čech コホモロジーが有限になる。
方針：長完全列の真ん中の三項を取り出し、有界性を使って次数を下げる。
規約：各表示の核も対象の族に属する。
使われ方：有限斉次自由表示と、その有限生成の核で使う。
-/
theorem projectiveCechFinite_of_shortExact_presentations
    (D : Obj → Finset ι ⥤ ModuleCat R)
    (hpresentation : ∀ M, ∃ (F K : Obj)
      (f : orderedCechComplex (D K) ⟶ orderedCechComplex (D F))
      (g : orderedCechComplex (D F) ⟶ orderedCechComplex (D M))
      (hfg : f ≫ g = 0),
      (ShortComplex.mk f g hfg).ShortExact ∧
        ∀ q, Module.Finite R ((orderedCechComplex (D F)).homology q)) :
    ∀ M q, Module.Finite R ((orderedCechComplex (D M)).homology q) := by
  classical
  letI := Fintype.ofFinite ι
  apply projectiveCechFinite_of_bounded_of_exact
    (fun M q ↦ (orderedCechComplex (D M)).homology q) (Fintype.card ι)
  · intro M q hq
    let _ := ModuleCat.isZero_iff_subsingleton.mp (isZero_orderedCechHomology (D M) q hq)
    infer_instance
  · intro M q
    obtain ⟨F, K, f, g, hfg, hex, hfinite⟩ := hpresentation M
    let S := ShortComplex.mk f g hfg
    have hS : S.ShortExact := hex
    have hrel : (ComplexShape.up ℕ).Rel q (q + 1) := rfl
    let u := HomologicalComplex.homologyMap g q
    let v := hS.δ q (q + 1) hrel
    refine ⟨F, K, u.hom, v.hom, hfinite q, ?_⟩
    have he := hS.homology_exact₃ q (q + 1) hrel
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he

end SerrePositivity.AlgebraicGeometry
