module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFunctor

/-!
概要：非空の有限交叉の係数の自然同型から、Čech 複体の同型を作る。
方針：正の長さのタプルの台が非空であることを使い、各成分の同型を取る。
規約：増大項を含まない通常の Čech 複体を扱う。
使われ方：空交叉の環を指定せずに、Proj の標準開の切断と局所化の複体を比較する。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open CategoryTheory

variable {R ι : Type*} [CommRing R] [DecidableEq ι]
variable {D E : Finset ι ⥤ ModuleCat R}

/-- 正の長さのタプルに現れる添字集合は非空。 -/
theorem cechTupleSupport_nonempty {q : ℕ} (t : Fin (q + 1) → ι) :
    (cechTupleSupport t).Nonempty :=
  ⟨t 0, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩⟩

/-- 非空有限交叉の係数の同型を、Čech の一つの項に移す。 -/
def fullCechNonemptyTermEquiv
    (e : ∀ (s : Finset ι), s.Nonempty → (D.obj s ≅ E.obj s)) (q : ℕ) :
    FullCechCochains D (q + 1) ≃ₗ[R] FullCechCochains E (q + 1) :=
  LinearEquiv.piCongrRight fun t ↦
    (e (cechTupleSupport t) (cechTupleSupport_nonempty t)).toLinearEquiv

/-- 非空交叉での自然性は Čech の余境界との可換性を与える。 -/
theorem fullCechNonemptyTermEquiv_differential
    (e : ∀ (s : Finset ι), s.Nonempty → (D.obj s ≅ E.obj s))
    (he : ∀ {s t : Finset ι} (hs : s.Nonempty) (hst : s ⊆ t),
      D.map (homOfLE hst) ≫ (e t (Finset.Nonempty.mono hst hs)).hom =
        (e s hs).hom ≫ E.map (homOfLE hst)) (q : ℕ) :
    (fullCechNonemptyTermEquiv e (q + 1)).toLinearMap.comp
        (fullCechDifferential D (q + 1)) =
      (fullCechDifferential E (q + 1)).comp
        (fullCechNonemptyTermEquiv e q).toLinearMap := by
  apply LinearMap.ext
  intro a
  funext t
  change (e (cechTupleSupport t) (cechTupleSupport_nonempty t)).hom.hom
      (fullCechDifferential D (q + 1) a t) =
    fullCechDifferential E (q + 1) (fullCechNonemptyTermEquiv e q a) t
  simp only [fullCechDifferential_apply, map_sum, map_zsmul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have h := congrArg (fun f : D.obj (cechTupleSupport (t ∘ i.succAbove)) ⟶
      E.obj (cechTupleSupport t) ↦ f.hom (a (t ∘ i.succAbove)))
    (he (cechTupleSupport_nonempty (t ∘ i.succAbove)) (cechTupleSupport_face_subset t i))
  exact h

/-- 非空有限交叉の自然同型が与える、通常の全タプル Čech 複体の同型。 -/
def fullCechNonemptyComplexIso
    (e : ∀ (s : Finset ι), s.Nonempty → (D.obj s ≅ E.obj s))
    (he : ∀ {s t : Finset ι} (hs : s.Nonempty) (hst : s ⊆ t),
      D.map (homOfLE hst) ≫ (e t (Finset.Nonempty.mono hst hs)).hom =
        (e s hs).hom ≫ E.map (homOfLE hst)) :
    fullCechComplex D ≅ fullCechComplex E :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ (fullCechNonemptyTermEquiv e q).toModuleIso) (by
      intro i j hij
      have h : i + 1 = j := hij
      subst j
      change ModuleCat.ofHom (fullCechNonemptyTermEquiv e i).toLinearMap ≫
          (fullCechComplex E).d i (i + 1) =
        (fullCechComplex D).d i (i + 1) ≫
          ModuleCat.ofHom (fullCechNonemptyTermEquiv e (i + 1)).toLinearMap
      simp only [fullCechComplex, CochainComplex.of_d]
      apply ModuleCat.hom_ext
      simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using
        (fullCechNonemptyTermEquiv_differential e he i).symm)

end SerrePositivity.AlgebraicGeometry
