module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.NativeCoreIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.PointFamily
public import SerrePositivity.DifferentialGraded.Category.Tensor
public import SerrePositivity.DifferentialGraded.Category.Basic
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence
public import SerrePositivity.DifferentialGraded.Complexes.Perturbation
public import SerrePositivity.KST.SConstruction.DGFunctorWhiskering
public import SerrePositivity.KST.SConstruction.DGFunctorNativeComposition

/-!
概要：零複体と非零可縮 disk を持つ有限 dg 入力で、native 同値と実同型を区別する。
方針：二対象の Hom を実複体圏から引き戻し、既存の disk 収縮を使う。
規約：懸垂 map の不存在は、この試験入力だけからは主張しない。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
open CategoryTheory CategoryTheory.Limits MonoidalCategory DifferentialGraded HomologicalComplex
open CochainComplex HomComplex
open scoped _root_.Simplicial ZeroObject

abbrev NativeDiskPair := ULift.{v} Bool
variable (R : Type u) [CommRing R]

def nativeDiskPairValue (x : NativeDiskPair.{v}) : Complex R :=
  if x.down then complexDisk R 0 else 0

instance nativeDiskPairDGCategory : DGCategory R NativeDiskPair.{v} :=
  inducedDGCategory R (nativeDiskPairValue R)

/-- 同じ二対象から実複体への全 Hom 評価。 -/
def nativeDiskPairEvaluation : DGFunctor R NativeDiskPair.{v} (Complex R) :=
  inducedDGEvaluation R (nativeDiskPairValue R)

lemma nativeDiskPairEvaluation_homIso (x y : NativeDiskPair.{v}) :
    IsIso ((nativeDiskPairEvaluation R).map x y) := by
  change IsIso (𝟙 _)
  infer_instance

lemma nativeDiskPair_closed_zero (X Y : Complex R) :
    complexClosedHomEquiv R X Y 0 = 0 := by
  apply Cochain.ofHom_injective
  rw [complexClosedHomEquiv_cochain]
  simp [cycleFromUnit]

/-- 複体圏の H⁰ では零と disk は同型である。 -/
def nativeDiskPairComplexH0Iso :
    (toHomotopy R (Complex R)).obj (ForgetEnrichment.of (Complex R) (0 : Complex R)) ≅
      (toHomotopy R (Complex R)).obj (ForgetEnrichment.of (Complex R) (complexDisk R 0)) := by
  have hz : (𝟙 ((toHomotopy R (Complex R)).obj
      (ForgetEnrichment.of (Complex R) (0 : Complex R)))) = 0 := by
    rw [← CategoryTheory.Functor.map_id (toHomotopy R (Complex R))]
    have h := (complex_H0_eq_iff R (0 : Complex R) 0 (𝟙 _) 0).2
      ⟨by simpa only [complexClosedHomEquiv_id, nativeDiskPair_closed_zero] using
        Homotopy.ofEq ((isZero_zero (Complex R)).eq_of_src (𝟙 _) 0)⟩
    simpa only [CategoryTheory.Functor.map_zero] using h
  have hd : (𝟙 ((toHomotopy R (Complex R)).obj
      (ForgetEnrichment.of (Complex R) (complexDisk R 0)))) = 0 := by
    rw [← CategoryTheory.Functor.map_id (toHomotopy R (Complex R))]
    have h := (complex_H0_eq_iff R (complexDisk R 0) (complexDisk R 0) (𝟙 _) 0).2
      ⟨by simpa only [complexClosedHomEquiv_id, nativeDiskPair_closed_zero] using
        complexDiskContractingHomotopy R 0⟩
    simpa only [CategoryTheory.Functor.map_zero] using h
  exact { hom := 0, inv := 0, hom_inv_id := by simp [hz], inv_hom_id := by simp [hd] }

/-- 同じ有限入力の中でも、二対象は H⁰ で同型。 -/
def nativeDiskPairH0Iso :
    (toHomotopy R NativeDiskPair.{v}).obj
        (ForgetEnrichment.of (Complex R) (ULift.up false)) ≅
      (toHomotopy R NativeDiskPair.{v}).obj
        (ForgetEnrichment.of (Complex R) (ULift.up true)) := by
  let E := nativeDiskPairEvaluation.{u,v} R
  letI := E.onHomotopy_full_of_homIso (nativeDiskPairEvaluation_homIso R)
  letI := E.onHomotopy_faithful_of_homIso (nativeDiskPairEvaluation_homIso R)
  exact E.onHomotopy.preimageIso (nativeDiskPairComplexH0Iso R)

/-- 零と非零 disk の実複体同型は存在しない。 -/
lemma nativeDiskPair_no_complexIso [Nontrivial R] :
    ¬ Nonempty ((0 : Complex R) ≅ complexDisk R 0) := by
  rintro ⟨e⟩
  have he : e.inv = 0 := (isZero_zero (Complex R)).eq_of_tgt _ _
  have hi : (𝟙 (complexDisk R 0)) = 0 := by simpa [he] using e.inv_hom_id.symm
  have hm : (𝟙 (𝟙_ (ModuleCat R))) = 0 := by
    have h := congrArg (fun f : complexDisk R 0 ⟶ complexDisk R 0 =>
      (complexDiskX₀ R 0).inv ≫ f.f 0 ≫ (complexDiskX₀ R 0).hom) hi
    simpa using h
  exact one_ne_zero (ConcreteCategory.congr_hom hm (1 : R))

/-- 同じ有限 dg 入力の二対象は、実閉射の圏では同型でない。 -/
lemma nativeDiskPair_no_closedIso [Nontrivial R] :
    ¬ Nonempty ((ForgetEnrichment.of (Complex R) (ULift.up false : NativeDiskPair.{v})) ≅
      ForgetEnrichment.of (Complex R) (ULift.up true : NativeDiskPair.{v})) := by
  rintro ⟨e⟩
  exact nativeDiskPair_no_complexIso R
    ⟨(closedToComplex R).mapIso ((nativeDiskPairEvaluation R).onClosed.mapIso e)⟩

/-- 入力の対象宇宙を合わせるための、一対象環の同じ対象ラベル。 -/
abbrev NativeDiskUnitInput := ULift.{v} PUnit.{1}

instance nativeDiskUnitDGCategory : DGCategory R NativeDiskUnitInput.{v} :=
  inducedDGCategory R (fun _ : NativeDiskUnitInput.{v} => (PUnit.unit : PUnit.{1}))

def nativeDiskUnitProjection : DGFunctor R NativeDiskUnitInput.{v} PUnit.{1} :=
  inducedDGEvaluation R (fun _ : NativeDiskUnitInput.{v} => (PUnit.unit : PUnit.{1}))

/-- 一対象入力から二対象入力への指定対象関手の族。 -/
def nativeDiskPointFamily : DGFunctor R NativeDiskPair.{v}
    (DGFunctor R NativeDiskUnitInput.{v} NativeDiskPair.{v}) :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgPointFamily R NativeDiskPair.{v}).comp
    (KST.SConstruction.dgFunctorPreDG R PUnit.{1} NativeDiskPair.{v}
      NativeDiskUnitInput.{v} (nativeDiskUnitProjection R))

/-- 二つの指定対象関手は、入力の正本 native Hom の中で可逆に結ばれる。 -/
def nativeDiskPointVertexIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := KST.SConstruction.dgFunctorNativeMappingSpace R
      NativeDiskUnitInput.{v} NativeDiskPair.{v})
      (KST.SConstruction.dgFunctorNativeMappingVertex R _ _
        ((nativeDiskPointFamily R).obj (ULift.up false)))
      (KST.SConstruction.dgFunctorNativeMappingVertex R _ _
        ((nativeDiskPointFamily R).obj (ULift.up true))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality.dgCoreVertexIsoOfH0 R _
    ((nativeDiskPointFamily R).onHomotopy.mapIso (nativeDiskPairH0Iso R))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.ClosureFunctoriality
