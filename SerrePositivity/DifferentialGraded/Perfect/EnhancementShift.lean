module
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementShiftComparison
public import Mathlib.CategoryTheory.Shift.Induced

/-! # 実際のdg shiftによる射影的perfect H⁰の整数shift

主Perfとの完全忠実同値を使い、各整数の実際のdg shiftのH⁰にzero/add coherenceを誘導する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- Perf同値の逆関手と実際のdg shiftのH⁰との自然比較を、順関手の完全忠実性で引き戻す。 -/
def perfectDGModuleInverseShiftIso (S : Set D) (s : ℤ) :
    (perfectDGModuleHomotopyEquivalence A D S).inverse ⋙
      (perfectDGModuleShiftDG A D S s).onHomotopy ≅
    shiftFunctor (PerfectModuleCategoryOver A D S) s ⋙
      (perfectDGModuleHomotopyEquivalence A D S).inverse := by
  let e := perfectDGModuleHomotopyEquivalence A D S
  exact ((Functor.FullyFaithful.ofFullyFaithful e.functor).whiskeringRight
    (PerfectModuleCategoryOver A D S)).preimageIso
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft e.inverse (perfectDGModuleShiftHomotopyPerfectIso A D S s) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e.counitIso (shiftFunctor (PerfectModuleCategoryOver A D S) s) ≪≫
        (shiftFunctor (PerfectModuleCategoryOver A D S) s).leftUnitor ≪≫
        (shiftFunctor (PerfectModuleCategoryOver A D S) s).rightUnitor.symm ≪≫
        Functor.isoWhiskerLeft (shiftFunctor (PerfectModuleCategoryOver A D S) s)
          e.counitIso.symm ≪≫
        (Functor.associator _ _ _).symm)

/-- 実際のdg shiftのH⁰に、Mathlibの誘導shift構造でzero/addとその整合性を与える。 -/
instance perfectDGHomotopyHasShift (S : Set D) :
    HasShift (PerfectDGHomotopyCategoryOver A D S) ℤ :=
  (Functor.FullyFaithful.ofFullyFaithful (perfectDGModuleToPerfect A D S)).hasShift
    (fun s => (perfectDGModuleShiftDG A D S s).onHomotopy)
    (perfectDGModuleShiftHomotopyPerfectIso A D S)

/-- 各整数の誘導shift関手は、実際の全Hom dg shiftからのH⁰関手そのものである。 -/
lemma perfectDGHomotopy_shiftFunctor (S : Set D) (s : ℤ) :
    shiftFunctor (PerfectDGHomotopyCategoryOver A D S) s =
      (perfectDGModuleShiftDG A D S s).onHomotopy := rfl

/-- H⁰ shiftの加法性は元のdg関手が誘導するH⁰加法性から継承する。 -/
instance perfectDGHomotopyShiftAdditive (S : Set D) (s : ℤ) :
    (shiftFunctor (PerfectDGHomotopyCategoryOver A D S) s).Additive := by
  rw [perfectDGHomotopy_shiftFunctor]
  infer_instance

/-- 完全忠実比較により誘導したshiftの下で、順関手の比較を元の自然同型として公開する。 -/
instance perfectDGModuleHomotopyEquivalenceFunctorCommShift (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).functor.CommShift ℤ :=
  Functor.CommShift.ofHasShiftOfFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful (perfectDGModuleToPerfect A D S))
    (fun s => (perfectDGModuleShiftDG A D S s).onHomotopy)
    (perfectDGModuleShiftHomotopyPerfectIso A D S)

/-- 順関手の整合的比較から、逆関手の比較をMathlibの随伴APIで構成する。 -/
instance perfectDGModuleHomotopyEquivalenceInverseCommShift (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).inverse.CommShift ℤ :=
  (perfectDGModuleHomotopyEquivalence A D S).commShiftInverse ℤ

/-- Perfとの同値の単位・余単位も整数shiftと整合する。 -/
instance perfectDGModuleHomotopyEquivalenceCommShift (S : Set D) :
    (perfectDGModuleHomotopyEquivalence A D S).CommShift ℤ :=
  (perfectDGModuleHomotopyEquivalence A D S).commShift_of_functor ℤ

/-- 元のH⁰比較関手も、実際のdg shiftから誘導した整数shiftと整合する。 -/
instance perfectDGModuleToPerfectCommShift (S : Set D) :
    (perfectDGModuleToPerfect A D S).CommShift ℤ :=
  perfectDGModuleHomotopyEquivalenceFunctorCommShift A D S

/-- 主Perfへの整合的shift比較は、実際のdg shiftから構成した自然同型そのものである。 -/
lemma perfectDGModuleToPerfect_commShiftIso (S : Set D) (s : ℤ) :
    (perfectDGModuleToPerfect A D S).commShiftIso s =
      perfectDGModuleShiftHomotopyPerfectIso A D S s := rfl

end SerrePositivity.DifferentialGraded
