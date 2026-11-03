module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! # dg 加群の全 Hom 射の shift による判定
概要：H⁰ の全単射性を全ての源 shift で検査し、全 Hom の擬同型を得る。
方針：実正規化 shift 同型と Hom 複体の shift 比較の可換図式を使う。
規約：H⁰ だけから他次数の同型を結論しない。使われ方：Perf の Morita 不変性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory HomologicalComplex SerrePositivity.DifferentialGraded
open SerrePositivity.DifferentialGraded.Morita

/-- 指定した二対象上の H⁰ の全単射性は、実 Hom 射の零次数の擬同型を与える。 -/
lemma dgHom_quasiIsoAt_zero_of_bijective {A : Type u} [CommRing A]
    {C : Type v} [DGCategory A C] {B : Type w} [DGCategory A B]
    (T : DGFunctor A C B) (x y : ClosedCategory A C)
    (h : Function.Bijective (fun f : (toHomotopy A C).obj x ⟶ (toHomotopy A C).obj y =>
      T.onHomotopy.map f)) : QuasiIsoAt (T.map x y) 0 := by
  let eS := homotopyHomologyEquiv A C x y
  let eT := homotopyHomologyEquiv A B (T.onClosed.obj x) (T.onClosed.obj y)
  have he : eT ∘ (fun f => T.onHomotopy.map f) = homologyMap (T.map x y) 0 ∘ eS :=
    funext (fun f => T.homotopyHomologyEquiv_map_naturality f)
  have hb := eT.bijective.comp h
  have hb' : Function.Bijective (homologyMap (T.map x y) 0 ∘ eS) := he ▸ hb
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact (Function.Bijective.of_comp_iff _ eS.bijective).mp hb'

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : DGFunctor A (RightModule A D) (RightModule A E))

/-- 実 dg 加群関手の source shift は、元の Hom 射の対応する次数を検査する。 -/
lemma dgModuleHom_shift_zero_iff (M N : RightModule A D) (s : ℤ) :
    QuasiIsoAt (T.map (shiftModule s M) N) 0 ↔ QuasiIsoAt (T.map M N) (-s) := by
  let e := normalizedDGModuleFunctorShiftIso A D E T s M
  let W := eHomWhiskerRight (Complex A) e.inv
    (ForgetEnrichment.of (Complex A) (T.obj N))
  have : IsIso W := by
    change IsIso (((eHomFunctor (Complex A) (ModuleCategory A E)).map e.inv.op).app _)
    infer_instance
  calc
    QuasiIsoAt (T.map (shiftModule s M) N) 0 ↔
        QuasiIsoAt (T.map (shiftModule s M) N ≫ W) 0 :=
      (quasiIsoAt_iff_comp_right _ W 0).symm
    _ ↔ QuasiIsoAt ((T.map (shiftModule s M) N ≫ W) ≫
        (moduleHomSourceShiftIso A E (T.obj M) (T.obj N) s).hom) 0 :=
      (quasiIsoAt_iff_comp_right _ _ 0).symm
    _ ↔ QuasiIsoAt ((moduleHomSourceShiftIso A D M N s).hom ≫
        (CategoryTheory.shiftFunctor (Complex A) (-s)).map (T.map M N)) 0 := by
      rw [Category.assoc, criterionPerfDGFunctorHom_sourceShift]
    _ ↔ QuasiIsoAt ((CategoryTheory.shiftFunctor (Complex A) (-s)).map (T.map M N)) 0 :=
      quasiIsoAt_iff_comp_left _ _ 0
    _ ↔ QuasiIsoAt (T.map M N) (-s) :=
      CochainComplex.quasiIsoAt_shift_iff _ (-s) 0 (-s) (by omega)

/-- 全 source shift での H⁰ 判定から、元の実 Hom 複体の擬同型を得る。 -/
lemma dgModuleHom_quasiIso_of_shift_zero (M N : RightModule A D)
    (h : ∀ s : ℤ, QuasiIsoAt (T.map (shiftModule s M) N) 0) : QuasiIso (T.map M N) := by
  rw [quasiIso_iff]
  intro i
  simpa only [neg_neg] using (dgModuleHom_shift_zero_iff A D E T M N (-i)).mp (h (-i))

end SerrePositivity.KST.SConstruction
