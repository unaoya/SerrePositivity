module

public import SerrePositivity.AlgebraicGeometry.OpenCoverIntSequentialAugmentedExact
public import SerrePositivity.AlgebraicGeometry.AffineSectionAlgebraAugmentation
public import SerrePositivity.AlgebraicGeometry.SchemeStructureIntCechRefinement

/-!
概要：アフィン被覆の同じ実際の構造層の Frobenius 係数の増大 Čech 完全性。
方針：準連接な構造層の各有限段の計算を、同じ加法群と順極限の比較で移す。
規約：正次数だけでなく、元の増大項の単射性と零次の完全性を含む Čech 版。
使われ方：実際のアフィンの係数比較と、二重 Čech の列の完全性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
universe u
variable (Y : Scheme.{u}) [IsAffine Y] (p : ℕ) (hp : p.Prime)
variable (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
variable {ι : Type} [DecidableEq ι] [Fintype ι]

/-- 同じアフィン被覆での実際の Frobenius 係数の増大完全性の Čech 版。
BS17 Thm 2.9 のアフィン比較に用いる、Stacks 30.2.6 の計算に対応する形。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem affineSchemeStructurePerfectCech_augmentedExact (U : ι → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcU : (⨆ i, U i) = ⊤) :
    Function.Injective (fullCechDifferential
      (openCoverCechDiagram (frobeniusRingDiagram Y.presheaf p hp hY) U) 0) ∧
      ∀ k, Function.Exact (fullCechDifferential
        (openCoverCechDiagram (frobeniusRingDiagram Y.presheaf p hp hY) U) k)
        (fullCechDifferential
          (openCoverCechDiagram (frobeniusRingDiagram Y.presheaf p hp hY) U) (k + 1)) := by
  letI : LinearOrder ι := cechFiniteIndexOrder ι
  let P := schemeModuleCechPresheaf (schemeStructureModule Y) ⋙
    ModuleCat.restrictScalars (RingHom.id Γ(Y, ⊤))
  have hP := affineSchemeModuleCech_acyclic (RingHom.id Γ(Y, ⊤))
    (schemeStructureModule Y) U hU hcU
  let S := frobeniusRingSequentialDiagram Y.presheaf p hp hY
  have hS (n : ℕ) :
      Function.Injective (fullCechDifferential (openCoverCechDiagram (S.obj n) U) 0) ∧
        ∀ k, Function.Exact (fullCechDifferential (openCoverCechDiagram (S.obj n) U) k)
          (fullCechDifferential (openCoverCechDiagram (S.obj n) U) (k + 1)) := by
    let D := openCoverCechDiagram P U
    let E := openCoverCechDiagram (S.obj n) U
    let e : ∀ T, D.obj T ≃+ E.obj T := fun _ ↦ AddEquiv.refl _
    have he : ∀ {T V : Finset ι} (h : T ⊆ V) (x : D.obj T),
        e V ((D.map (homOfLE h)).hom x) = (E.map (homOfLE h)).hom (e T x) := by intros; rfl
    exact ⟨fullCechAdditiveCoefficientEquiv_zero_injective D E e he hP.injective_zero,
      fun k ↦ fullCechAdditiveCoefficientEquiv_exact D E e he k (hP.exact k)⟩
  have hc := openCoverIntSequential_augmentedExact S U hS
  let e := Functor.isoWhiskerLeft (openCoverCechIndexFunctor U)
    (frobeniusRingSequentialColimitIso Y.presheaf p hp hY)
  exact ⟨fullCechCoefficientEquiv_zero_injective e hc.1,
    fun k ↦ fullCechCoefficientEquiv_exact e k (hc.2 k)⟩

end SerrePositivity.AlgebraicGeometry
