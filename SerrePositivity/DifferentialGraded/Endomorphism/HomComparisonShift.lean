module
public import SerrePositivity.DifferentialGraded.Endomorphism.HomComparisonRetracts
public import SerrePositivity.DifferentialGraded.Functor.ModuleShiftOpposite

/-! # 全次数Hom比較と反変shiftの可換図式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex

lemma complexShiftIsoOfSumZero_hom {A : Type u} [CommRing A]
    {K L : Complex A} {s t : ℤ} (α : Cochain K L s) (hα : δ s (s + 1) α = 0)
    (β : Cochain L K t) (hst : s + t = 0)
    (hαβ : α.comp β hst = Cochain.ofHom (𝟙 K))
    (hβα : β.comp α (by omega : t + s = 0) = Cochain.ofHom (𝟙 L)) :
    (complexShiftIsoOfSumZero A α hα β hst hαβ hβα).hom = complexShiftComparison A α hα := by
  have ht : t = -s := by omega
  subst t
  rfl

lemma dgHomMap_contra_naturality {A : Type u} [CommRing A]
    {C : Type v} {B : Type w} [DGCategory A C] [DGCategory A B]
    (F : DGFunctor A C B) (T : C) (x y : Cᵒᵖ) :
    (representable A T).map x y ≫
        homPostcompose ((representable A T).obj x) (F.map y.unop T) =
      (F.op.comp (representable A (F.obj T))).map x y ≫
        homPrecompose (F.map x.unop T) ((F.op.comp (representable A (F.obj T))).obj y) := by
  apply closedFamily_of_action A
    (M := representable A T) (N := F.op.comp (representable A (F.obj T)))
    (fun z => F.map z.unop T)
  intro x y p r n hn f v
  exact F.map_forward A f v (by omega)

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma contraShiftComparison_naturality
    (F G : DGFunctor A (RightModule A D)ᵒᵖ (Complex A))
    (a : ∀ x : (RightModule A D)ᵒᵖ, F.obj x ⟶ G.obj x)
    (h : ∀ x y, F.map x y ≫ homPostcompose (F.obj x) (a y) =
      G.map x y ≫ homPrecompose (a x) (G.obj y))
    (s : ℤ) (M : RightModule A D) :
    a (op (shiftModule s M)) ≫ (DGFunctor.moduleShiftOppImageIso A D G s M).hom =
      (DGFunctor.moduleShiftOppImageIso A D F s M).hom ≫
        (CategoryTheory.shiftFunctor (Complex A) (-s)).map (a (op M)) := by
  change a _ ≫ (complexShiftIsoOfSumZero A _ _ _ _ _ _).hom =
    (complexShiftIsoOfSumZero A _ _ _ _ _ _).hom ≫ _
  rw [complexShiftIsoOfSumZero_hom, complexShiftIsoOfSumZero_hom]
  apply HomologicalComplex.hom_ext
  intro i
  rw [comp_f, comp_f, complexShiftComparison_f, complexShiftComparison_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  exact (closedFamily_action A a h (op (shiftModule s M)) (op M) (-s) i (i + -s)
    rfl (moduleShiftInElement A D s M) v).symm

variable (E : RightModule A D)

/-- 指定Hom比較の始域の整数shiftに対する全次数可換図式。 -/
lemma endomorphismHomComparison_shift_square (s : ℤ) (M T : RightModule A D) :
    (endomorphismModuleHom A D E).map (shiftModule s M) T ≫
        (DGFunctor.moduleShiftOppImageIso A D
          ((endomorphismModuleHom A D E).op.comp
            (representable A ((endomorphismModuleHom A D E).obj T))) s M).hom =
      (DGFunctor.moduleShiftOppImageIso A D (representable A T) s M).hom ≫
        (CategoryTheory.shiftFunctor (Complex A) (-s)).map
          ((endomorphismModuleHom A D E).map M T) :=
  contraShiftComparison_naturality A D (representable A T)
    ((endomorphismModuleHom A D E).op.comp
      (representable A ((endomorphismModuleHom A D E).obj T)))
    (fun x => (endomorphismModuleHom A D E).map x.unop T)
    (dgHomMap_contra_naturality (endomorphismModuleHom A D E) T) s M

lemma endomorphismHomComparison_shift (s : ℤ) (M T : RightModule A D)
    (hM : QuasiIso ((endomorphismModuleHom A D E).map M T)) :
    QuasiIso ((endomorphismModuleHom A D E).map (shiftModule s M) T) := by
  have := hM
  have h := endomorphismHomComparison_shift_square A D E s M T
  have hs : QuasiIso ((endomorphismModuleHom A D E).map (shiftModule s M) T ≫
      (DGFunctor.moduleShiftOppImageIso A D
        ((endomorphismModuleHom A D E).op.comp
          (representable A ((endomorphismModuleHom A D E).obj T))) s M).hom) := by
    rw [h]
    infer_instance
  exact quasiIso_of_comp_right ((endomorphismModuleHom A D E).map (shiftModule s M) T)
    (DGFunctor.moduleShiftOppImageIso A D
      ((endomorphismModuleHom A D E).op.comp
        (representable A ((endomorphismModuleHom A D E).obj T))) s M).hom

instance endomorphismHomComparisonLocusStableUnderShift :
    (endomorphismHomComparisonLocus A D E).IsStableUnderShift ℤ where
  isStableUnderShiftBy s := ⟨by
    intro X hX
    apply (endomorphismHomComparisonLocus A D E).prop_of_iso
      (((moduleToHomotopy A D).commShiftIso s).app X.as)
    intro T
    exact endomorphismHomComparison_shift A D E s X.as T (hX T)⟩

end SerrePositivity.DifferentialGraded
