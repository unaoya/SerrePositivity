module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor

/-!
概要：有限交叉の係数の短完全列を、全タプル Čech 複体の短完全列にする。
方針：各タプルの成分の完全性を使い、前像を成分ごとに選ぶ。
規約：被覆の添字集合を固定し、分離的な標準開の計算に使う。
使われ方：閉厚化の全タプル Čech 長完全列を、Rees 側の核の評価と結ぶ。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]
variable {D E F : Finset ι ⥤ ModuleCat R}

instance fullCechComplexFunctor_preservesZeroMorphisms :
    (fullCechComplexFunctor (R := R) (ι := ι)).PreservesZeroMorphisms where
  map_zero _ _ := by
    ext q a
    rfl

/-- 各交叉の係数列が短完全なら、全タプル Čech 複体の列も短完全。 -/
theorem fullCechComplex_shortExact (f : D ⟶ E) (g : E ⟶ F) (hfg : f ≫ g = 0)
    (hS : ∀ T, (ShortComplex.mk (f.app T) (g.app T)
      (congrArg (fun h : D ⟶ F ↦ h.app T) hfg)).ShortExact) :
    ((ShortComplex.mk f g hfg).map fullCechComplexFunctor).ShortExact := by
  classical
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro q
  let S := ((ShortComplex.mk f g hfg).map fullCechComplexFunctor).map
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) q)
  change S.ShortExact
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mpr
    intro y
    constructor
    · intro h
      have hp (t : Fin (q + 1) → ι) :
          ∃ x, (f.app (cechTupleSupport t)).hom x = y t :=
        ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hS _).exact (y t)).mp
          (congrFun h t)
      exact ⟨fun t ↦ (hp t).choose, funext fun t ↦ (hp t).choose_spec⟩
    · rintro ⟨x, rfl⟩
      exact S.moduleCat_zero_apply x
  · apply (ModuleCat.mono_iff_injective S.f).mpr
    intro x y h
    funext t
    exact (ModuleCat.mono_iff_injective (f.app (cechTupleSupport t))).mp
      (hS _).mono_f (congrFun h t)
  · apply (ModuleCat.epi_iff_surjective S.g).mpr
    intro y
    have h (t : Fin (q + 1) → ι) :=
      (ModuleCat.epi_iff_surjective (g.app (cechTupleSupport t))).mp (hS _).epi_g (y t)
    exact ⟨fun t ↦ (h t).choose, funext fun t ↦ (h t).choose_spec⟩

end SerrePositivity.AlgebraicGeometry
