module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Endomorphism.Perfect
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementOperations
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Adjunction
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import SerrePositivity.DifferentialGraded.Endomorphism.Basic
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement
public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.HomComparison
public import Mathlib.CategoryTheory.Adjunction.Limits
public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.EnhancementComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.Derived.Functors
public import SerrePositivity.DifferentialGraded.Endomorphism.Module
public import SerrePositivity.DifferentialGraded.Endomorphism.Shift
public import SerrePositivity.DifferentialGraded.Endomorphism.Scalar.PerfectStability
public import SerrePositivity.DifferentialGraded.Tensor.ScalarExtension.CategoriesAndModules

/-!
# Endomorphism.Enhancement

## 概要
13 本に分かれていた同主題の構成と比較をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## EnhancementAdjunction（旧 SerrePositivity/DifferentialGraded/Endomorphism/EnhancementAdjunction.lean） -/

/-! # U13 dg enhancementの閉零圏への実際の再構成随伴の制限 -/

@[expose] public section EnhancementAdjunction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

def perfectEndomorphismTensorClosedInclusionIso :
    (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed ⋙
        (endomorphismModuleTensor A D E.val).onClosed ≅
      (perfectEndomorphismTensorDG A D S E).onClosed ⋙
        (perfectDGModuleInclusion A D S).onClosed :=
  (EnrichedFunctor.forgetComp
    (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ)
    (endomorphismModuleTensor A D E.val)).symm ≪≫
    eqToIso (congrArg DGFunctor.onClosed
      (perfectEndomorphismTensorDG_inclusion_square A D S E).symm) ≪≫
    EnrichedFunctor.forgetComp (perfectEndomorphismTensorDG A D S E)
      (perfectDGModuleInclusion A D S)

variable (hgen : endomorphismThickGeneratesPerfect A D S E)

def perfectEndomorphismHomClosedInclusionIso :
    (perfectDGModuleInclusion A D S).onClosed ⋙ (endomorphismModuleHom A D E.val).onClosed ≅
      (perfectEndomorphismDG A D S E hgen).onClosed ⋙
        (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed :=
  (EnrichedFunctor.forgetComp (perfectDGModuleInclusion A D S)
    (endomorphismModuleHom A D E.val)).symm ≪≫
    eqToIso (congrArg DGFunctor.onClosed
      (perfectEndomorphismDG_inclusion_square A D S E hgen).symm) ≪≫
    EnrichedFunctor.forgetComp (perfectEndomorphismDG A D S E hgen)
      (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ)

/-- 全加群上の実際の随伴を、HPかつperfectな実際のdg対象の閉零圏へ制限する。 -/
def perfectEndomorphismEnhancementAdjunction :
    (perfectEndomorphismTensorDG A D S E).onClosed ⊣
      (perfectEndomorphismDG A D S E hgen).onClosed := by
  have : (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed.Full := by
    unfold perfectDGModuleInclusion
    infer_instance
  have : (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed.Faithful := by
    unfold perfectDGModuleInclusion
    infer_instance
  have : (perfectDGModuleInclusion A D S).onClosed.Full := by
    unfold perfectDGModuleInclusion
    infer_instance
  have : (perfectDGModuleInclusion A D S).onClosed.Faithful := by
    unfold perfectDGModuleInclusion
    infer_instance
  exact (endomorphismModuleAdjunction A D E.val).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful
      (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed)
    (Functor.FullyFaithful.ofFullyFaithful (perfectDGModuleInclusion A D S).onClosed)
    (perfectEndomorphismTensorClosedInclusionIso A D S E)
    (perfectEndomorphismHomClosedInclusionIso A D S E hgen)

lemma perfectEndomorphismEnhancement_left_triangle
    (N : ClosedCategory A (PerfectDGModule A (EndomorphismObject E.val))) :
    (perfectEndomorphismTensorDG A D S E).onClosed.map
        ((perfectEndomorphismEnhancementAdjunction A D S E hgen).unit.app N) ≫
      (perfectEndomorphismEnhancementAdjunction A D S E hgen).counit.app
        ((perfectEndomorphismTensorDG A D S E).onClosed.obj N) = 𝟙 _ :=
  (perfectEndomorphismEnhancementAdjunction A D S E hgen).left_triangle_components N

lemma perfectEndomorphismEnhancement_right_triangle
    (M : ClosedCategory A (PerfectDGModuleOver A D S)) :
    (perfectEndomorphismEnhancementAdjunction A D S E hgen).unit.app
        ((perfectEndomorphismDG A D S E hgen).onClosed.obj M) ≫
      (perfectEndomorphismDG A D S E hgen).onClosed.map
        ((perfectEndomorphismEnhancementAdjunction A D S E hgen).counit.app M) = 𝟙 _ :=
  (perfectEndomorphismEnhancementAdjunction A D S E hgen).right_triangle_components M

/-- enhancement制限の単位を包含で写すと、全加群の元の単位の可換図式になる。 -/
lemma perfectEndomorphismEnhancementUnit_inclusion
    (N : ClosedCategory A (PerfectDGModule A (EndomorphismObject E.val))) :
    (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed.map
        ((perfectEndomorphismEnhancementAdjunction A D S E hgen).unit.app N) =
      (endomorphismModuleUnit A D E.val).app
          ((perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onClosed.obj N) ≫
        (endomorphismModuleHom A D E.val).onClosed.map
          ((perfectEndomorphismTensorClosedInclusionIso A D S E).hom.app N) ≫
        (perfectEndomorphismHomClosedInclusionIso A D S E hgen).hom.app
          ((perfectEndomorphismTensorDG A D S E).onClosed.obj N) := by
  unfold perfectEndomorphismEnhancementAdjunction
  exact Adjunction.map_restrictFullyFaithful_unit_app _ _ _ _ _ N

/-- enhancement制限の余単位を包含で写すと、全加群の元の合成評価の可換図式になる。 -/
lemma perfectEndomorphismEnhancementCounit_inclusion
    (M : ClosedCategory A (PerfectDGModuleOver A D S)) :
    (perfectDGModuleInclusion A D S).onClosed.map
        ((perfectEndomorphismEnhancementAdjunction A D S E hgen).counit.app M) =
      (perfectEndomorphismTensorClosedInclusionIso A D S E).inv.app
          ((perfectEndomorphismDG A D S E hgen).onClosed.obj M) ≫
        (endomorphismModuleTensor A D E.val).onClosed.map
          ((perfectEndomorphismHomClosedInclusionIso A D S E hgen).inv.app M) ≫
        (endomorphismModuleCounit A D E.val).app
          ((perfectDGModuleInclusion A D S).onClosed.obj M) := by
  unfold perfectEndomorphismEnhancementAdjunction
  exact Adjunction.map_restrictFullyFaithful_counit_app _ _ _ _ _ M

end SerrePositivity.DifferentialGraded
end

end EnhancementAdjunction

/-! ## EnhancementShiftTriangles（旧 SerrePositivity/DifferentialGraded/Endomorphism/EnhancementShiftTriangles.lean） -/

/-! # U13 enhancementとの比較正方形の整合的shiftと三角性 -/

@[expose] public section EnhancementShiftTriangles
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

local instance : (perfectEndomorphismHomToPerfect A D S E hgen).CommShift ℤ :=
  perfectEndomorphismHomCommShift A D S E hgen
local instance : (perfectEndomorphismHomToPerfect A D S E hgen).IsTriangulated :=
  perfectEndomorphismHomIsTriangulated A D S E hgen

/-- 実際のdg比較のH⁰に、U13比較を通して主Perfと整合するshiftを入れる。 -/
@[instance_reducible]
def perfectEndomorphismDGHomotopyCommShift :
    (perfectEndomorphismDG A D S E hgen).onHomotopy.CommShift ℤ :=
  Functor.CommShift.ofComp (perfectEndomorphismDerivedComparison A D S E hgen) ℤ

local instance : (perfectEndomorphismDG A D S E hgen).onHomotopy.CommShift ℤ :=
  perfectEndomorphismDGHomotopyCommShift A D S E hgen

lemma perfectEndomorphismDerivedComparison_commShift :
    NatTrans.CommShift (perfectEndomorphismDerivedComparison A D S E hgen).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (perfectEndomorphismDerivedComparison A D S E hgen) ℤ

/-- U13との既存比較正方形を三角関手の正方形へ強化する。 -/
lemma perfectEndomorphismDGHomotopyIsTriangulated :
    (perfectEndomorphismDG A D S E hgen).onHomotopy.IsTriangulated := by
  let := perfectEndomorphismDerivedComparison_commShift A D S E hgen
  exact (Functor.isTriangulated_iff_comp_right
    (perfectEndomorphismDerivedComparison A D S E hgen)).2 inferInstance

/-- enhancement比較と主Perf比較の、三角形の圏における自然な正方形。 -/
def perfectEndomorphismEnhancementTriangleSquareIso :
    (perfectEndomorphismDG A D S E hgen).onHomotopy.mapTriangle ⋙
        (perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ).mapTriangle ≅
      (perfectDGModuleToPerfect A D S).mapTriangle ⋙
        (perfectEndomorphismHomToPerfect A D S E hgen).mapTriangle := by
  let := perfectEndomorphismDerivedComparison_commShift A D S E hgen
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (perfectEndomorphismDerivedComparison A D S E hgen) ≪≫
      Functor.mapTriangleCompIso _ _

end SerrePositivity.DifferentialGraded
end

end EnhancementShiftTriangles

/-! ## EnhancementHomotopyAdjunction（旧 SerrePositivity/DifferentialGraded/Endomorphism/EnhancementHomotopyAdjunction.lean） -/

/-! # U13 enhancementのH⁰への実際のtensor–Hom随伴制限 -/

@[expose] public section EnhancementHomotopyAdjunction
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

def perfectEndomorphismTensorHomotopyInclusionIso :
    (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onHomotopy ⋙
        (endomorphismModuleTensor A D E.val).onHomotopy ≅
      (perfectEndomorphismTensorDG A D S E).onHomotopy ⋙
        (perfectDGModuleInclusion A D S).onHomotopy :=
  eqToIso ((DGFunctor.onHomotopy_comp _ _).symm.trans
    ((congrArg DGFunctor.onHomotopy
      (perfectEndomorphismTensorDG_inclusion_square A D S E).symm).trans
        (DGFunctor.onHomotopy_comp _ _)))

variable (hgen : endomorphismThickGeneratesPerfect A D S E)

def perfectEndomorphismHomHomotopyInclusionIso :
    (perfectDGModuleInclusion A D S).onHomotopy ⋙
        (endomorphismModuleHom A D E.val).onHomotopy ≅
      (perfectEndomorphismDG A D S E hgen).onHomotopy ⋙
        (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onHomotopy :=
  eqToIso ((DGFunctor.onHomotopy_comp _ _).symm.trans
    ((congrArg DGFunctor.onHomotopy
      (perfectEndomorphismDG_inclusion_square A D S E hgen).symm).trans
        (DGFunctor.onHomotopy_comp _ _)))

/-- 実際のH⁰ tensorとHomの随伴。選択された逆関手で置換しない。 -/
def perfectEndomorphismEnhancementHomotopyAdjunction :
    (perfectEndomorphismTensorDG A D S E).onHomotopy ⊣
      (perfectEndomorphismDG A D S E hgen).onHomotopy :=
  (endomorphismHomotopyAdjunction A D E.val).restrictFullyFaithful
    (Functor.FullyFaithful.ofFullyFaithful
      (perfectDGModuleInclusion A (EndomorphismObject E.val) Set.univ).onHomotopy)
    (Functor.FullyFaithful.ofFullyFaithful (perfectDGModuleInclusion A D S).onHomotopy)
    (perfectEndomorphismTensorHomotopyInclusionIso A D S E)
    (perfectEndomorphismHomHomotopyInclusionIso A D S E hgen)

end SerrePositivity.DifferentialGraded
end

end EnhancementHomotopyAdjunction

/-! ## EnhancementTensorComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/EnhancementTensorComparison.lean） -/

/-! # 実際のenhancement tensorと主Perf tensorの自然比較 -/

@[expose] public section EnhancementTensorComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

/-- 既存のHom比較をU13同値の逆で運んだ、二つの実際の右随伴の比較。 -/
def perfectEndomorphismEnhancementRightComparison :
    (perfectDGModuleHomotopyEquivalence A D S).inverse ⋙
        (perfectEndomorphismDG A D S E hgen).onHomotopy ≅
      perfectEndomorphismHomToPerfect A D S E hgen ⋙
        (perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).inverse := by
  let P := perfectDGModuleHomotopyEquivalence A D S
  let Q := perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ
  apply Functor.fullyFaithfulCancelRight Q.functor
  exact
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft P.inverse (perfectEndomorphismDerivedComparison A D S E hgen) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight P.counitIso (perfectEndomorphismHomToPerfect A D S E hgen) ≪≫
      Functor.leftUnitor _) ≪≫
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (perfectEndomorphismHomToPerfect A D S E hgen) Q.counitIso ≪≫
      Functor.rightUnitor _).symm

/-- 実際のenhancement随伴をU13同値で運び、既存のHom比較で右随伴を揃える。 -/
def perfectEndomorphismEnhancementTransportedAdjunction :
    (perfectEndomorphismTensorDG A D S E).onHomotopy ⋙
        perfectDGModuleToPerfect A D S ⊣
      perfectEndomorphismHomToPerfect A D S E hgen ⋙
        (perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).inverse :=
  ((perfectEndomorphismEnhancementHomotopyAdjunction A D S E hgen).comp
    (perfectDGModuleHomotopyEquivalence A D S).toAdjunction).ofNatIsoRight
      (perfectEndomorphismEnhancementRightComparison A D S E hgen)

/-- 実際のtensorのH⁰と主Perfのtensorの正方形。随伴の一意性で構成する。 -/
def perfectEndomorphismEnhancementTensorComparison :
    (perfectEndomorphismTensorDG A D S E).onHomotopy ⋙
        perfectDGModuleToPerfect A D S ≅
      perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ ⋙
        perfectEndomorphismTensorToPerfect A D S E := by
  exact (perfectEndomorphismEnhancementTransportedAdjunction A D S E hgen).leftAdjointUniq
    ((perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).toAdjunction.comp
      (perfectEndomorphismAdjunction A D S E hgen))

lemma perfectEndomorphismEnhancementTensorComparison_unit :
    (perfectEndomorphismEnhancementTransportedAdjunction A D S E hgen).unit ≫
      Functor.whiskerRight (perfectEndomorphismEnhancementTensorComparison A D S E hgen).hom
        (perfectEndomorphismHomToPerfect A D S E hgen ⋙
          (perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).inverse) =
    ((perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).toAdjunction.comp
      (perfectEndomorphismAdjunction A D S E hgen)).unit :=
  Adjunction.unit_leftAdjointUniq_hom _ _

lemma perfectEndomorphismEnhancementTensorComparison_counit :
    Functor.whiskerLeft
        (perfectEndomorphismHomToPerfect A D S E hgen ⋙
          (perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).inverse)
        (perfectEndomorphismEnhancementTensorComparison A D S E hgen).hom ≫
      ((perfectDGModuleHomotopyEquivalence A (EndomorphismObject E.val) Set.univ).toAdjunction.comp
        (perfectEndomorphismAdjunction A D S E hgen)).counit =
    (perfectEndomorphismEnhancementTransportedAdjunction A D S E hgen).counit :=
  Adjunction.leftAdjointUniq_hom_counit _ _

end SerrePositivity.DifferentialGraded
end

end EnhancementTensorComparison

/-! ## EnhancementTensorTriangles（旧 SerrePositivity/DifferentialGraded/Endomorphism/EnhancementTensorTriangles.lean） -/

/-! # 実際のenhancement tensorと主Perf比較のshift・三角性 -/

@[expose] public section EnhancementTensorTriangles
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

local instance : (perfectEndomorphismTensorToPerfect A D S E).CommShift ℤ :=
  perfectEndomorphismTensorCommShift A D S E
local instance : (perfectEndomorphismTensorToPerfect A D S E).IsTriangulated :=
  perfectEndomorphismTensorIsTriangulated A D S E

@[instance_reducible]
def perfectEndomorphismTensorDGHomotopyCommShift :
    (perfectEndomorphismTensorDG A D S E).onHomotopy.CommShift ℤ :=
  Functor.CommShift.ofComp (perfectEndomorphismEnhancementTensorComparison A D S E hgen) ℤ

lemma perfectEndomorphismEnhancementTensorComparison_commShift :
    letI := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
    NatTrans.CommShift (perfectEndomorphismEnhancementTensorComparison A D S E hgen).hom ℤ :=
  Functor.CommShift.ofComp_compatibility
    (perfectEndomorphismEnhancementTensorComparison A D S E hgen) ℤ

lemma perfectEndomorphismTensorDGHomotopyIsTriangulated :
    letI := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
    (perfectEndomorphismTensorDG A D S E).onHomotopy.IsTriangulated := by
  let := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
  let := perfectEndomorphismEnhancementTensorComparison_commShift A D S E hgen
  exact (Functor.isTriangulated_iff_comp_right
    (perfectEndomorphismEnhancementTensorComparison A D S E hgen)).2 inferInstance

def perfectEndomorphismEnhancementTensorTriangleSquareIso :
    letI := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
    (perfectEndomorphismTensorDG A D S E).onHomotopy.mapTriangle ⋙
        (perfectDGModuleToPerfect A D S).mapTriangle ≅
      (perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ).mapTriangle ⋙
        (perfectEndomorphismTensorToPerfect A D S E).mapTriangle := by
  let := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
  let := perfectEndomorphismEnhancementTensorComparison_commShift A D S E hgen
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (perfectEndomorphismEnhancementTensorComparison A D S E hgen) ≪≫
      Functor.mapTriangleCompIso _ _

end SerrePositivity.DifferentialGraded
end

end EnhancementTensorTriangles

/-! ## CoproductHomComparison（旧 SerrePositivity/DifferentialGraded/Endomorphism/CoproductHomComparison.lean） -/

/-! # compactな始域から見た導来Homの余積比較

余積自体をcompactと仮定しない。compact性は始域Pとそのtensor像にのみ要求する。
-/

@[expose] public section CoproductHomComparison
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Preadditive
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (E : RightModule A D)
variable (hE : moduleHomotopicallyProjective A D (ForgetEnrichment.of (Complex A) E))

lemma endomorphismDerivedHom_additive : (endomorphismDerivedHom A D E hE).Additive := by
  rw [Localization.functor_additive_iff (moduleHomotopyToDerivedClosed A D)
    (moduleHomotopyQuasiIso A D)]
  exact Functor.additive_of_iso (endomorphismDerivedHomHomotopyIso A D E hE)

local instance : (endomorphismDerivedHom A D E hE).Additive :=
  endomorphismDerivedHom_additive A D E hE

include hE in
lemma endomorphismDerivedTensor_additive : (endomorphismDerivedTensor A D E).Additive :=
  (endomorphismDerivedAdjunction A D E hE).left_adjoint_additive

variable {J : Type u} (F : J → DerivedModuleCategory A D)

lemma endomorphismDerivedHom_sigmaComparison_projection (i : J) :
    sigmaComparison (endomorphismDerivedHom A D E hE) F ≫
        (endomorphismDerivedHom A D E hE).map (moduleDerivedCoproductProjection A D F i) =
      moduleDerivedCoproductProjection A (EndomorphismObject E)
        (fun j => (endomorphismDerivedHom A D E hE).obj (F j)) i := by
  apply Sigma.hom_ext
  intro j
  rw [ι_comp_sigmaComparison_assoc, ← CategoryTheory.Functor.map_comp]
  by_cases hji : j = i
  · subst j
    rw [moduleDerivedCoproductProjection_self, CategoryTheory.Functor.map_id,
      moduleDerivedCoproductProjection_self]
  · rw [moduleDerivedCoproductProjection_ne A D F j i hji, Functor.map_zero,
      moduleDerivedCoproductProjection_ne A (EndomorphismObject E) _ j i hji]

lemma endomorphismDerivedHom_sigmaHom_injective
    (P : DerivedModuleCategory A (EndomorphismObject E))
    (hP : moduleCompact A (EndomorphismObject E) P) :
    Function.Injective (fun f : P ⟶ ∐ fun j => (endomorphismDerivedHom A D E hE).obj (F j) =>
      f ≫ sigmaComparison (endomorphismDerivedHom A D E hE) F) := by
  intro f g hfg
  change f ≫ sigmaComparison (endomorphismDerivedHom A D E hE) F =
    g ≫ sigmaComparison (endomorphismDerivedHom A D E hE) F at hfg
  apply sub_eq_zero.mp
  apply moduleCompact_hom_ext_zero A (EndomorphismObject E) hP _ (f - g)
  intro i
  rw [← endomorphismDerivedHom_sigmaComparison_projection A D E hE F i,
    sub_comp, ← Category.assoc, ← Category.assoc, hfg, sub_self]

lemma endomorphismDerivedHom_sigmaHom_surjective
    (P : DerivedModuleCategory A (EndomorphismObject E))
    (hLP : moduleCompact A D ((endomorphismDerivedTensor A D E).obj P)) :
    Function.Surjective (fun f : P ⟶ ∐ fun j => (endomorphismDerivedHom A D E hE).obj (F j) =>
      f ≫ sigmaComparison (endomorphismDerivedHom A D E hE) F) := by
  classical
  let := endomorphismDerivedTensor_additive A D E hE
  let adj := endomorphismDerivedAdjunction A D E hE
  intro f
  obtain ⟨t, g, hg⟩ := hLP J F ((adj.homEquiv P (∐ F)).symm f)
  refine ⟨∑ j ∈ t, adj.homEquiv P (F j) (g j) ≫
    Sigma.ι (fun j => (endomorphismDerivedHom A D E hE).obj (F j)) j, ?_⟩
  dsimp only
  rw [sum_comp]
  have he := congrArg (adj.homAddEquiv P (∐ F)) hg
  have hx : (adj.homAddEquiv P (∐ F)) ((adj.homEquiv P (∐ F)).symm f) = f :=
    (adj.homEquiv P (∐ F)).apply_symm_apply f
  rw [hx] at he
  simp only [map_sum] at he
  calc
    _ = ∑ j ∈ t, adj.homEquiv P (∐ F) (g j ≫ Sigma.ι F j) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Category.assoc, ι_comp_sigmaComparison]
      exact (adj.homEquiv_naturality_right (g j) (Sigma.ι F j)).symm
    _ = f := he

lemma endomorphismDerivedHom_sigmaHom_bijective
    (P : DerivedModuleCategory A (EndomorphismObject E))
    (hP : moduleCompact A (EndomorphismObject E) P)
    (hLP : moduleCompact A D ((endomorphismDerivedTensor A D E).obj P)) :
    Function.Bijective (fun f : P ⟶ ∐ fun j => (endomorphismDerivedHom A D E hE).obj (F j) =>
      f ≫ sigmaComparison (endomorphismDerivedHom A D E hE) F) :=
  ⟨endomorphismDerivedHom_sigmaHom_injective A D E hE F P hP,
    endomorphismDerivedHom_sigmaHom_surjective A D E hE F P hLP⟩

end SerrePositivity.DifferentialGraded
end

end CoproductHomComparison

/-! ## HomPreservesCoproducts（旧 SerrePositivity/DifferentialGraded/Endomorphism/HomPreservesCoproducts.lean） -/

/-! # perfectな指定対象に対する導来Homの余積保存

compact⇒Perfは外部から明示して受け取る。無限余積のcompact性は要求しない。
-/

@[expose] public section HomPreservesCoproducts
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (compactToPerfect : ∀ P : DerivedModuleCategory A (EndomorphismObject E.val),
  moduleCompact A (EndomorphismObject E.val) P →
    modulePerfect A (EndomorphismObject E.val) P)

include compactToPerfect
lemma perfectEndomorphismTensor_obj_compact
    {P : DerivedModuleCategory A (EndomorphismObject E.val)}
    (hP : moduleCompact A (EndomorphismObject E.val) P) :
    moduleCompact A D ((endomorphismDerivedTensor A D E.val).obj P) :=
  modulePerfectOver_compact A D
    (perfectEndomorphismTensor_obj_perfect A D S E (compactToPerfect P hP))

lemma perfectEndomorphismHom_sigmaComparison_isIso {J : Type u}
    (F : J → DerivedModuleCategory A D) :
    IsIso (sigmaComparison (endomorphismDerivedHom A D E.val E.property.1) F) := by
  apply moduleDerived_isIso_of_compact_hom_bijective A (EndomorphismObject E.val)
  intro P hP
  exact endomorphismDerivedHom_sigmaHom_bijective A D E.val E.property.1 F P hP
    (perfectEndomorphismTensor_obj_compact A D S E compactToPerfect hP)

lemma perfectEndomorphismHom_preservesCoproduct {J : Type u}
    (F : J → DerivedModuleCategory A D) :
    PreservesColimit (Discrete.functor F)
      (endomorphismDerivedHom A D E.val E.property.1) := by
  let := perfectEndomorphismHom_sigmaComparison_isIso A D S E compactToPerfect F
  exact PreservesCoproduct.of_iso_comparison _ F

end SerrePositivity.DifferentialGraded
end

end HomPreservesCoproducts

/-! ## DerivedUnitAll（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedUnitAll.lean） -/

/-! # 実際の導来随伴の単位の全対象での可逆性 -/

@[expose] public section DerivedUnitAll
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (compactToPerfect : ∀ P : DerivedModuleCategory A (EndomorphismObject E.val),
  moduleCompact A (EndomorphismObject E.val) P →
    modulePerfect A (EndomorphismObject E.val) P)
include compactToPerfect

lemma perfectEndomorphismHom_preservesCoproductsOfShape (J : Type u) :
    PreservesColimitsOfShape (Discrete J)
      (endomorphismDerivedHom A D E.val E.property.1) where
  preservesColimit {K} := by
    let := perfectEndomorphismHom_preservesCoproduct A D S E compactToPerfect
      (K.obj ∘ Discrete.mk)
    exact preservesColimit_of_iso_diagram _ Discrete.natIsoFunctor.symm

variable (hgen : endomorphismThickGeneratesPerfect A D S E)
include hgen

/-- 単位の同型性を、実際の標準解像度と余積保存で全End導来対象へ拡張する。 -/
lemma endomorphismDerivedUnit_isIso_all
    (N : DerivedModuleCategory A (EndomorphismObject E.val)) :
    IsIso ((endomorphismDerivedUnit A D E.val E.property.1).app N) := by
  let L := endomorphismDerivedTensor A D E.val
  let R := endomorphismDerivedHom A D E.val E.property.1
  let := endomorphismDerivedTensorCommShift A D E.val E.property.1
  let := endomorphismDerivedHomCommShift A D E.val E.property.1
  let := endomorphismDerivedTensorIsTriangulated A D E.val E.property.1
  let := endomorphismDerivedHomIsTriangulated A D E.val E.property.1
  let := endomorphismDerivedTensor_additive A D E.val E.property.1
  let := endomorphismDerivedHom_additive A D E.val E.property.1
  let := endomorphismDerivedUnit_commShift A D E.val E.property.1
  let P := derivedNatTransIsoLocus A (EndomorphismObject E.val) (L ⋙ R)
    (endomorphismDerivedUnit A D E.val E.property.1)
  change P N
  apply moduleLocalizing_all A (EndomorphismObject E.val) P
  · intro J F hF
    let := (endomorphismDerivedAdjunction A D E.val E.property.1).leftAdjoint_preservesColimits
    let := perfectEndomorphismHom_preservesCoproductsOfShape A D S E compactToPerfect J
    exact derivedNatTransIsoLocus_coproduct A (EndomorphismObject E.val) (L ⋙ R)
      (endomorphismDerivedUnit A D E.val E.property.1) F hF
  · intro X hX
    exact endomorphismDerivedUnit_isIso_onPerfect A D S E hgen ⟨X, hX⟩

end SerrePositivity.DifferentialGraded
end

end DerivedUnitAll

/-! ## DerivedEquivalence（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedEquivalence.lean） -/

/-! # 明示したcompact生成仮定の下での主導来圏全体の再構成同値

thick生成だけから全導来圏同値は結論しない。指定対象によるcompact生成と、
外部compact⇒Perf入力をそれぞれ明示して受け取る。
-/

@[expose] public section DerivedEquivalence
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (compactToPerfect : ∀ P : DerivedModuleCategory A (EndomorphismObject E.val),
  moduleCompact A (EndomorphismObject E.val) P →
    modulePerfect A (EndomorphismObject E.val) P)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)
variable (hCG : endomorphismCompactGenerator A D E.val)
include compactToPerfect hgen hCG

/-- 単位の全対象での可逆性、右三角恒等式、Homの保守性から余単位も可逆となる。 -/
lemma endomorphismDerivedCounit_isIso_all (X : DerivedModuleCategory A D) :
    IsIso ((endomorphismDerivedCounit A D E.val E.property.1).app X) := by
  let adj := endomorphismDerivedAdjunction A D E.val E.property.1
  let R := endomorphismDerivedHom A D E.val E.property.1
  let := endomorphismDerivedUnit_isIso_all A D S E compactToPerfect hgen (R.obj X)
  have hu : IsIso (adj.unit.app (R.obj X)) := by
    change IsIso ((endomorphismDerivedUnit A D E.val E.property.1).app (R.obj X))
    infer_instance
  let := hu
  have he : R.map (adj.counit.app X) = inv (adj.unit.app (R.obj X)) := by
    apply (cancel_epi (adj.unit.app (R.obj X))).1
    rw [adj.right_triangle_components, IsIso.hom_inv_id]
    rfl
  have hm : IsIso (R.map (adj.counit.app X)) := by rw [he]; infer_instance
  let := hm
  exact endomorphismDerivedHom_reflectsIso A D E.val E.property.1 hCG (adj.counit.app X)

/-- 実際の導来tensorとHomを両方向に持つ同値。 -/
def endomorphismDerivedEquivalence :
    DerivedModuleCategory A (EndomorphismObject E.val) ≌ DerivedModuleCategory A D := by
  letI (N : DerivedModuleCategory A (EndomorphismObject E.val)) :
      IsIso ((endomorphismDerivedAdjunction A D E.val E.property.1).unit.app N) :=
    endomorphismDerivedUnit_isIso_all A D S E compactToPerfect hgen N
  letI (X : DerivedModuleCategory A D) :
      IsIso ((endomorphismDerivedAdjunction A D E.val E.property.1).counit.app X) :=
    endomorphismDerivedCounit_isIso_all A D S E compactToPerfect hgen hCG X
  exact (endomorphismDerivedAdjunction A D E.val E.property.1).toEquivalence

lemma endomorphismDerivedEquivalence_functor :
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).functor =
      endomorphismDerivedTensor A D E.val := rfl

lemma endomorphismDerivedEquivalence_inverse :
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).inverse =
      endomorphismDerivedHom A D E.val E.property.1 := rfl

lemma endomorphismDerivedEquivalence_unit :
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).unitIso.hom =
      endomorphismDerivedUnit A D E.val E.property.1 := rfl

lemma endomorphismDerivedEquivalence_counit :
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).counitIso.hom =
      endomorphismDerivedCounit A D E.val E.property.1 := rfl

end SerrePositivity.DifferentialGraded
end

end DerivedEquivalence

/-! ## DerivedEquivalenceTriangles（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedEquivalenceTriangles.lean） -/

/-! # 全主導来圏同値の実際のshiftと三角性 -/

@[expose] public section DerivedEquivalenceTriangles
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (compactToPerfect : ∀ P : DerivedModuleCategory A (EndomorphismObject E.val),
  moduleCompact A (EndomorphismObject E.val) P →
    modulePerfect A (EndomorphismObject E.val) P)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)
variable (hCG : endomorphismCompactGenerator A D E.val)

local instance :
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).inverse.CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E.val E.property.1

/-- 同値の両側に既存の実際のtensor/Hom shiftを使う。 -/
lemma endomorphismDerivedEquivalence_commShift :
    letI : (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).functor.CommShift ℤ :=
      endomorphismDerivedTensorCommShift A D E.val E.property.1
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).CommShift ℤ := by
  let : (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).functor.CommShift ℤ :=
    endomorphismDerivedTensorCommShift A D E.val E.property.1
  let := endomorphismDerivedTensorCommShift A D E.val E.property.1
  let := endomorphismDerivedHomCommShift A D E.val E.property.1
  apply Equivalence.CommShift.mk'
  change NatTrans.CommShift (endomorphismDerivedUnit A D E.val E.property.1) ℤ
  exact endomorphismDerivedUnit_commShift A D E.val E.property.1

lemma endomorphismDerivedEquivalence_isTriangulated :
    letI : (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).functor.CommShift ℤ :=
      endomorphismDerivedTensorCommShift A D E.val E.property.1
    letI := endomorphismDerivedEquivalence_commShift A D S E compactToPerfect hgen hCG
    (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).IsTriangulated := by
  let : (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).functor.CommShift ℤ :=
    endomorphismDerivedTensorCommShift A D E.val E.property.1
  let := endomorphismDerivedEquivalence_commShift A D S E compactToPerfect hgen hCG
  exact Equivalence.IsTriangulated.mk' _
    (endomorphismDerivedTensorIsTriangulated A D E.val E.property.1)

/-- 同値のtensorをPerfへ制限した正方形は、既存の実際のtensor制限と一致する。 -/
def endomorphismDerivedEquivalencePerfectTensorSquare :
    perfectEndomorphismTensorToPerfect A D S E ⋙ perfectModuleInclusion A D S ≅
      perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ⋙
        (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).functor :=
  perfectEndomorphismTensorInclusionIso A D S E

/-- 逆関手HomのPerf包含正方形も、既存のPerf比較そのもの。 -/
def endomorphismDerivedEquivalencePerfectHomSquare :
    perfectEndomorphismHomToPerfect A D S E hgen ⋙
        perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ≅
      perfectModuleInclusion A D S ⋙
        (endomorphismDerivedEquivalence A D S E compactToPerfect hgen hCG).inverse :=
  perfectEndomorphismHomInclusionIso A D S E hgen

end SerrePositivity.DifferentialGraded
end

end DerivedEquivalenceTriangles

/-! ## DerivedEquivalenceCompactGenerator（旧 SerrePositivity/DifferentialGraded/Endomorphism/DerivedEquivalenceCompactGenerator.lean） -/

/-! # U13dを適用しcompact⇒Perf入力を除いたU14c

既存の入力付きAPIは保持する。Endの対象型は一対象なのでSmall.{u}の条件を満たす。
指定集合Sのthick生成と、全導来圏のcompact生成はそれぞれ明示する。
-/

@[expose] public section DerivedEquivalenceCompactGenerator
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits

lemma endomorphismCompactToPerfect (A : Type u) [CommRing A]
    {C : Type*} [DGCategory A C] (E : C)
    (N : DerivedModuleCategory A (EndomorphismObject E))
    (hN : moduleCompact A (EndomorphismObject E) N) :
    modulePerfect A (EndomorphismObject E) N :=
  (moduleCompact_iff_perfect A (EndomorphismObject E) N).1 hN

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)

lemma perfectEndomorphismHom_preservesCoproduct_ofPerfect {J : Type u}
    (F : J → DerivedModuleCategory A D) :
    PreservesColimit (Discrete.functor F) (endomorphismDerivedHom A D E.val E.property.1) :=
  perfectEndomorphismHom_preservesCoproduct A D S E (endomorphismCompactToPerfect A E.val) F

variable (hgen : endomorphismThickGeneratesPerfect A D S E)
include hgen

lemma endomorphismDerivedUnit_isIso_of_compact_ofThickGenerator
    (N : DerivedModuleCategory A (EndomorphismObject E.val))
    (hN : moduleCompact A (EndomorphismObject E.val) N) :
    IsIso ((endomorphismDerivedUnit A D E.val E.property.1).app N) :=
  endomorphismDerivedUnit_isIso_of_compact A D S E hgen
    (endomorphismCompactToPerfect A E.val) N hN

lemma endomorphismDerivedUnit_isIso_all_ofThickGenerator
    (N : DerivedModuleCategory A (EndomorphismObject E.val)) :
    IsIso ((endomorphismDerivedUnit A D E.val E.property.1).app N) :=
  endomorphismDerivedUnit_isIso_all A D S E (endomorphismCompactToPerfect A E.val) hgen N

variable (hCG : endomorphismCompactGenerator A D E.val)
include hCG

lemma endomorphismDerivedCounit_isIso_all_ofCompactGenerator (X : DerivedModuleCategory A D) :
    IsIso ((endomorphismDerivedCounit A D E.val E.property.1).app X) :=
  endomorphismDerivedCounit_isIso_all A D S E (endomorphismCompactToPerfect A E.val) hgen hCG X

def endomorphismDerivedEquivalence_ofCompactGenerator :
    DerivedModuleCategory A (EndomorphismObject E.val) ≌ DerivedModuleCategory A D :=
  endomorphismDerivedEquivalence A D S E (endomorphismCompactToPerfect A E.val) hgen hCG

lemma endomorphismDerivedEquivalence_ofCompactGenerator_functor :
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).functor =
      endomorphismDerivedTensor A D E.val := rfl

lemma endomorphismDerivedEquivalence_ofCompactGenerator_inverse :
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).inverse =
      endomorphismDerivedHom A D E.val E.property.1 := rfl

lemma endomorphismDerivedEquivalence_ofCompactGenerator_unit :
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).unitIso.hom =
      endomorphismDerivedUnit A D E.val E.property.1 := rfl

lemma endomorphismDerivedEquivalence_ofCompactGenerator_counit :
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).counitIso.hom =
      endomorphismDerivedCounit A D E.val E.property.1 := rfl

local instance :
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).inverse.CommShift ℤ :=
  endomorphismDerivedHomCommShift A D E.val E.property.1

lemma endomorphismDerivedEquivalence_ofCompactGenerator_commShift :
    letI : (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).functor.CommShift
        ℤ :=
      endomorphismDerivedTensorCommShift A D E.val E.property.1
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).CommShift ℤ :=
  endomorphismDerivedEquivalence_commShift A D S E (endomorphismCompactToPerfect A E.val) hgen hCG

lemma endomorphismDerivedEquivalence_ofCompactGenerator_isTriangulated :
    letI : (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).functor.CommShift
        ℤ :=
      endomorphismDerivedTensorCommShift A D E.val E.property.1
    letI := endomorphismDerivedEquivalence_ofCompactGenerator_commShift A D S E hgen hCG
    (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).IsTriangulated :=
  endomorphismDerivedEquivalence_isTriangulated A D S E
    (endomorphismCompactToPerfect A E.val) hgen hCG

def endomorphismDerivedEquivalence_ofCompactGenerator_PerfectTensorSquare :
    perfectEndomorphismTensorToPerfect A D S E ⋙ perfectModuleInclusion A D S ≅
      perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ⋙
        (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).functor :=
  endomorphismDerivedEquivalencePerfectTensorSquare A D S E
    (endomorphismCompactToPerfect A E.val) hgen hCG

def endomorphismDerivedEquivalence_ofCompactGenerator_PerfectHomSquare :
    perfectEndomorphismHomToPerfect A D S E hgen ⋙
        perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ≅
      perfectModuleInclusion A D S ⋙
        (endomorphismDerivedEquivalence_ofCompactGenerator A D S E hgen hCG).inverse :=
  endomorphismDerivedEquivalencePerfectHomSquare A D S E
    (endomorphismCompactToPerfect A E.val) hgen hCG

end SerrePositivity.DifferentialGraded
end

end DerivedEquivalenceCompactGenerator

/-! ## ScalarReconstructionTriangles（旧 SerrePositivity/DifferentialGraded/Endomorphism/ScalarReconstructionTriangles.lean） -/

/-! # 実際のenhancement再構成tensorと導来係数変更の三角比較 -/

@[expose] public section ScalarReconstructionTriangles
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

def perfectEndomorphismEnhancementScalarTensorComparison :
    (perfectEndomorphismTensorDG A D S E).onHomotopy ⋙
        (scalarPerfectHomotopyExtension φ D S ⋙
          perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
            (scalarPerfectGenerators φ D S)) ≅
      perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ ⋙
        (perfectEndomorphismTensorToPerfect A D S E ⋙ perfectScalarDerivedExtension φ D S) :=
  Functor.isoWhiskerLeft (perfectEndomorphismTensorDG A D S E).onHomotopy
      (scalarPerfectHomotopyComparison φ D S).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectEndomorphismEnhancementTensorComparison A D S E hgen)
      (perfectScalarDerivedExtension φ D S) ≪≫
    Functor.associator _ _ _

local instance : (scalarPerfectHomotopyExtension φ D S).CommShift ℤ :=
  scalarPerfectHomotopyExtensionCommShift φ D S
local instance : (perfectEndomorphismTensorToPerfect A D S E).CommShift ℤ :=
  perfectEndomorphismTensorCommShift A D S E
local instance : (perfectScalarDerivedExtension φ D S).CommShift ℤ :=
  perfectScalarDerivedExtensionCommShift φ D S

lemma perfectEndomorphismEnhancementScalarTensorComparison_commShift :
    letI := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
    NatTrans.CommShift
      (perfectEndomorphismEnhancementScalarTensorComparison φ D S E hgen).hom ℤ := by
  let := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
  let := scalarPerfectHomotopyComparison_commShift φ D S
  let := perfectEndomorphismEnhancementTensorComparison_commShift A D S E hgen
  simp only [perfectEndomorphismEnhancementScalarTensorComparison, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

def perfectEndomorphismEnhancementScalarTensorTriangleSquareIso :
    letI := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
    (perfectEndomorphismTensorDG A D S E).onHomotopy.mapTriangle ⋙
        (scalarPerfectHomotopyExtension φ D S ⋙
          perfectDGModuleToPerfect A' (ScalarExtension.DGBaseChange φ D)
            (scalarPerfectGenerators φ D S)).mapTriangle ≅
      (perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ).mapTriangle ⋙
        (perfectEndomorphismTensorToPerfect A D S E ⋙
          perfectScalarDerivedExtension φ D S).mapTriangle := by
  let := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
  let := perfectEndomorphismEnhancementScalarTensorComparison_commShift φ D S E hgen
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (perfectEndomorphismEnhancementScalarTensorComparison φ D S E hgen) ≪≫
      Functor.mapTriangleCompIso _ _

end SerrePositivity.DifferentialGraded
end

end ScalarReconstructionTriangles

/-! ## Compatibility（旧 SerrePositivity/DifferentialGraded/Endomorphism/Compatibility.lean） -/

/-! # 指定対象のEndとshift・underived係数変更の正方形

非flat係数変更でもunderived Endの正方形は構成できる。
導来係数変更との一致や全Homの係数変更の同型性は主張しない。
-/

@[expose] public section Compatibility
universe u v

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] (E : D)

/-- Endを取って係数変更した一対象dg圏から、係数変更した指定対象のEndへの比較。 -/
def endomorphismScalarComparison :
    DGFunctor A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
      (EndomorphismObject (show ScalarExtension.DGBaseChange φ D from E)) where
  obj _ := .point
  map _ _ := 𝟙 _
  map_id _ := by simp only [Category.comp_id]; rfl
  map_comp _ _ _ := by
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
    rfl

/-- 係数変更後のEndの包含は、元の包含の係数変更と可換。 -/
lemma endomorphismScalarComparison_square :
    (endomorphismScalarComparison φ D E).comp
      (endomorphismInclusion A' (show ScalarExtension.DGBaseChange φ D from E)) =
    ScalarExtension.dgFunctor φ (endomorphismInclusion A E) := by
  apply EnrichedFunctor.ext (Complex A')
    (F := (endomorphismScalarComparison φ D E).comp
      (endomorphismInclusion A' (show ScalarExtension.DGBaseChange φ D from E)))
    (G := ScalarExtension.dgFunctor φ (endomorphismInclusion A E)) (fun _ => rfl)
  intro x y
  simp only [DGFunctor.comp, EnrichedFunctor.comp_map, endomorphismScalarComparison,
    endomorphismInclusion, ScalarExtension.dgFunctor, Category.comp_id,
    CategoryTheory.Functor.map_id, eqToHom_refl]
  rfl

variable (A) [Small.{u} D]

/-- U13の実際のdg shiftに沿う、指定対象のEndと包含の可換正方形。 -/
lemma perfectEndomorphismShift_square (S : Set D) (E : PerfectDGModuleOver A D S) (s : ℤ) :
    (endomorphismMap A (perfectDGModuleShiftDG A D S s) E).comp
        (endomorphismInclusion A ((perfectDGModuleShiftDG A D S s).obj E)) =
      (endomorphismInclusion A E).comp (perfectDGModuleShiftDG A D S s) :=
  endomorphismMap_comp_inclusion A (perfectDGModuleShiftDG A D S s) E

end SerrePositivity.DifferentialGraded
end

end Compatibility

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "4.8.5.8" (partial := stronger-hyp) "仮定：小さい dg 圏 D、その指定範囲の完全 dg 加群 E、E の thick 生成と全導来圏での compact generator 性（Lean が強い：通常の dg 導来圏に限り、これらの生成仮定を追加する）。結論：End(E) 上の加群の通常の導来圏から D 上の導来圏への同値を構成し、正則 End(E) 加群を E と同定する（この仮定での HA の結論の一部に一致）。一般の C-線型 ∞ 圏での六条件の同値は含まれない。"] _root_.SerrePositivity.DifferentialGraded.endomorphismDerivedEquivalence_ofCompactGenerator
attribute [cite HA "7.1.2.1" (partial := stronger-hyp) "仮定：可換環 A、小さい dg 圏 D、指定した完全 dg 加群 E と thick 生成および導来圏の compact generator 性（Lean が強い：dg 加群の通常の導来圏と追加の thick 生成に限る）。結論：End(E) の dg 加群の導来圏と D の dg 加群の導来圏の同値を構成する（この仮定での認識定理の十分性の部分に一致）。任意の安定可呈示 ∞ 圏のスペクトル加群による表示と必要性は含まれない。"] _root_.SerrePositivity.DifferentialGraded.endomorphismDerivedEquivalence_ofCompactGenerator
attribute [cite HA "7.1.2.3" (partial := stronger-hyp) "仮定：小さい dg 圏と指定した完全 compact generator E、追加の thick 生成（Lean が強い：通常の dg 導来圏の場合）。結論：表示に用いる代数を End(E) と明示し、正則加群の像を E と同定する（この仮定での HA の結論の一部に一致）。環スペクトルの自己準同型代数との比較は含まれない。"] _root_.SerrePositivity.DifferentialGraded.endomorphismDerivedEquivalence_ofCompactGenerator
