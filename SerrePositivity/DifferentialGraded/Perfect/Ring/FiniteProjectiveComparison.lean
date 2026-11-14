module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.DifferentialGraded.Category.Tensor

public import SerrePositivity.HomologicalAlgebra.Complex.StrictlyPerfect
public import SerrePositivity.DifferentialGraded.Module.Functor
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import SerrePositivity.DifferentialGraded.Module.Left.CategoryComparison
public import SerrePositivity.DifferentialGraded.Derived.Projective
public import SerrePositivity.DifferentialGraded.Derived.Basic
public import SerrePositivity.DifferentialGraded.Perfect.Basic
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology
public import SerrePositivity.DifferentialGraded.Perfect.Compact.Enhancement

public import Mathlib.RingTheory.Finiteness.Cardinality
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import SerrePositivity.CategoryTheory.Triangulated.Padding
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Perfect.Ring.FiniteProjectiveComparison

## 概要
有界有限射影複体から主 Perf への比較と retract の次数幅帰納をまとめる。

## 方針
対応表の依存順に連結し、元の宣言・証明・名前空間を保持する。

## 規約
各元ファイルの section を分離し、variable・option の局所的な作用を保つ。

## 使われ方
DifferentialGraded の入口と、この主題を使う検査・下流モジュールから import する。
-/

/-! ## StrictComplexEnhancement（旧 SerrePositivity/DifferentialGraded/Perfect/StrictComplexEnhancement.lean） -/

/-! # 既存の有界有限射影複体の全Hom dg enhancement

strictlyPerfectComplexとPerfectHomotopyをそのまま使う。
一対象Aの主Perfとの同定は、別に有限生成・retractを照合して証明する。
-/

@[expose] public section StrictComplexEnhancement
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 既存の有界有限射影複体を対象とし、主Hom複体をそのまま持つ充満dg部分圏。 -/
abbrev StrictPerfectDGComplex := DGFullSubcategory (Complex A) (strictlyPerfectComplex A)

/-- 既存の有限射影対象から全非有界複体へのdg包含。 -/
def strictPerfectDGComplexInclusion : DGFunctor A (StrictPerfectDGComplex A) (Complex A) :=
  dgFullSubcategoryInclusion A (Complex A) (strictlyPerfectComplex A)

/-- 有限射影複体のH⁰包含は充満。 -/
instance strictPerfectDGComplexInclusionHomotopyFull :
    (strictPerfectDGComplexInclusion A).onHomotopy.Full := by
  dsimp [strictPerfectDGComplexInclusion]
  infer_instance

/-- 有限射影複体のH⁰包含は忠実。 -/
instance strictPerfectDGComplexInclusionHomotopyFaithful :
    (strictPerfectDGComplexInclusion A).onHomotopy.Faithful := by
  dsimp [strictPerfectDGComplexInclusion]
  infer_instance

/-- 有限射影dg複体のH⁰から、既存の全複体ホモトピー圏への比較。 -/
def strictPerfectDGComplexToHomotopy : HomotopyCategory A (StrictPerfectDGComplex A) ⥤
    _root_.HomotopyCategory (ModuleCat.{u} A) (.up ℤ) :=
  (strictPerfectDGComplexInclusion A).onHomotopy ⋙ complexHomotopyComparison A

/-- 比較像は元の複体を代表とするので、既存perfectHomotopyPropertyを満たす。 -/
lemma strictPerfectDGComplexToHomotopy_obj_perfect
    (X : HomotopyCategory A (StrictPerfectDGComplex A)) :
    perfectHomotopyProperty A ((strictPerfectDGComplexToHomotopy A).obj X) := by
  let M : StrictPerfectDGComplex A := ForgetEnrichment.to (Complex A) X.as
  exact (perfectHomotopyProperty_quotient A M.val).mpr M.property

/-- 有限射影dg複体のH⁰から既存PerfectHomotopyへの比較。 -/
def strictPerfectDGComplexToPerfect : HomotopyCategory A (StrictPerfectDGComplex A) ⥤
    PerfectHomotopy A :=
  (perfectHomotopyProperty A).lift (strictPerfectDGComplexToHomotopy A)
    (strictPerfectDGComplexToHomotopy_obj_perfect A)

/-- 既存PerfectHomotopyへの比較は充満。全Hom包含と全複体比較の充満性を継承する。 -/
instance strictPerfectDGComplexToPerfectFull : (strictPerfectDGComplexToPerfect A).Full := by
  dsimp [strictPerfectDGComplexToPerfect, strictPerfectDGComplexToHomotopy]
  infer_instance

/-- 既存PerfectHomotopyへの比較は忠実。同じHom複体と境界関係を使う。 -/
instance strictPerfectDGComplexToPerfectFaithful :
    (strictPerfectDGComplexToPerfect A).Faithful := by
  dsimp [strictPerfectDGComplexToPerfect, strictPerfectDGComplexToHomotopy]
  infer_instance

/-- 既存PerfectHomotopyの対象が持つ実際の有限射影代表を選んで、本質的全射性を得る。 -/
instance strictPerfectDGComplexToPerfectEssSurj : (strictPerfectDGComplexToPerfect A).EssSurj where
  mem_essImage X := by
    let P : Complex A := X.obj.as
    have hP : strictlyPerfectComplex A P := (perfectHomotopyProperty_quotient A P).mp X.property
    let M : StrictPerfectDGComplex A := ⟨P, hP⟩
    exact ⟨(toHomotopy A (StrictPerfectDGComplex A)).obj (ForgetEnrichment.of (Complex A) M),
      ⟨(perfectHomotopyProperty A).isoMk (Iso.refl _)⟩⟩

/-- 全Homと実際の有限射影代表により、比較は同値である。 -/
instance strictPerfectDGComplexToPerfectIsEquivalence :
    (strictPerfectDGComplexToPerfect A).IsEquivalence where

/-- 既存PerfectHomotopyの、主Homを持つdg enhancementによるH⁰表示。 -/
def strictPerfectDGComplexHomotopyEquivalence :
    HomotopyCategory A (StrictPerfectDGComplex A) ≌ PerfectHomotopy A :=
  (strictPerfectDGComplexToPerfect A).asEquivalence

end SerrePositivity.DifferentialGraded
end

end StrictComplexEnhancement

/-! ## StrictComplexEnhancementLinear（旧 SerrePositivity/DifferentialGraded/Perfect/StrictComplexEnhancementLinear.lean） -/

/-! # 既存PerfectHomotopyの全Hom dg表示における線形性と包含の比較 -/

@[expose] public section StrictComplexEnhancementLinear
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 全複体ホモトピー圏への比較は加法的。H⁰包含と複体比較の合成として継承する。 -/
instance strictPerfectDGComplexToHomotopyAdditive :
    (strictPerfectDGComplexToHomotopy A).Additive := by
  dsimp [strictPerfectDGComplexToHomotopy]
  infer_instance

/-- 全複体ホモトピー圏への比較は主Hom由来のA線形性を保つ。 -/
instance strictPerfectDGComplexToHomotopyLinear :
    (strictPerfectDGComplexToHomotopy A).Linear A := by
  dsimp [strictPerfectDGComplexToHomotopy]
  infer_instance

/-- 既存PerfectHomotopyへの制限は加法性を保つ。 -/
instance strictPerfectDGComplexToPerfectAdditive :
    (strictPerfectDGComplexToPerfect A).Additive := by
  dsimp [strictPerfectDGComplexToPerfect]
  infer_instance

/-- 既存PerfectHomotopyへの比較はA線形。既存の充満部分圏の射の外延性を使う。 -/
instance strictPerfectDGComplexToPerfectLinear : (strictPerfectDGComplexToPerfect A).Linear A where
  map_smul f a := (perfectHomotopyProperty A).hom_ext
    ((strictPerfectDGComplexToHomotopy A).map_smul a f)

/-- 選択したH⁰同値の順関手は加法的で、逆関手にも加法性が移る。 -/
instance strictPerfectDGComplexHomotopyEquivalenceFunctorAdditive :
    (strictPerfectDGComplexHomotopyEquivalence A).functor.Additive :=
  strictPerfectDGComplexToPerfectAdditive A

/-- 選択したH⁰同値の順関手はA線形で、逆関手にも線形性が移る。 -/
instance strictPerfectDGComplexHomotopyEquivalenceFunctorLinear :
    (strictPerfectDGComplexHomotopyEquivalence A).functor.Linear A :=
  strictPerfectDGComplexToPerfectLinear A

/-- 既存perfect包含を経由する比較は、元の全複体ホモトピー圏への比較と自然同型で一致する。 -/
def strictPerfectDGComplexToPerfectCompInclusion :
    strictPerfectDGComplexToPerfect A ⋙ perfectHomotopyInclusion A ≅
      strictPerfectDGComplexToHomotopy A :=
  (perfectHomotopyProperty A).liftCompιIso _ _

end SerrePositivity.DifferentialGraded
end

end StrictComplexEnhancementLinear

/-! ## StrictComplexProjective（旧 SerrePositivity/DifferentialGraded/Perfect/StrictComplexProjective.lean） -/

/-! # 既存の有限射影複体から一対象A上の主射影的dg加群へ -/

@[expose] public section StrictComplexProjective
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 有界な各次数の射影性から既存のK-projective判定を使う。 -/
lemma strictlyPerfectComplex_isKProjective (P : Complex A)
    (hP : strictlyPerfectComplex A P) : P.IsKProjective := by
  obtain ⟨a, b, ha, hb⟩ := hP.1
  let := hb
  let (n : ℤ) : Module.Projective A (P.X n) := (hP.2 n).2
  exact CochainComplex.isKProjective_of_projective P b

/-- 有限射影複体を一対象Aのdg加群へ移すと、全Hom endの意味で射影的である。 -/
lemma strictlyPerfectComplex_ringModule_homotopicallyProjective (P : Complex A)
    (hP : strictlyPerfectComplex A P) :
    moduleHomotopicallyProjective A PUnit.{1}
      (ForgetEnrichment.of (Complex A) (ringModule A P)) :=
  (ringModule_homotopicallyProjective_iff A (ringModule A P)).2
    (strictlyPerfectComplex_isKProjective A P hP)

end SerrePositivity.DifferentialGraded
end

end StrictComplexProjective

/-! ## StrictComplexDerived（旧 SerrePositivity/DifferentialGraded/Perfect/StrictComplexDerived.lean） -/

/-! # 有限射影複体のH⁰から主dg加群導来圏への完全忠実な比較 -/

@[expose] public section StrictComplexDerived
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 有限射影複体を実際の一対象Aのdg加群へ送るdg関手。 -/
def strictPerfectDGComplexToRingModule :
    DGFunctor A (StrictPerfectDGComplex A) (RightModule A PUnit.{1}) :=
  DGFunctor.comp (strictPerfectDGComplexInclusion A) (ringConstantDG A)

instance strictPerfectDGComplexToRingModuleHomotopyFull :
    (strictPerfectDGComplexToRingModule A).onHomotopy.Full := by
  rw [strictPerfectDGComplexToRingModule, DGFunctor.onHomotopy_comp]
  infer_instance

instance strictPerfectDGComplexToRingModuleHomotopyFaithful :
    (strictPerfectDGComplexToRingModule A).onHomotopy.Faithful := by
  rw [strictPerfectDGComplexToRingModule, DGFunctor.onHomotopy_comp]
  infer_instance

/-- 実際のdg比較のH⁰に、既存の準同型局所化を合成する。 -/
def strictPerfectDGComplexToDerived : HomotopyCategory A (StrictPerfectDGComplex A) ⥤
    DerivedModuleCategory A PUnit.{1} :=
  (strictPerfectDGComplexToRingModule A).onHomotopy ⋙ moduleHomotopyToDerivedClosed A PUnit.{1}

instance strictPerfectDGComplexToDerivedFull : (strictPerfectDGComplexToDerived A).Full where
  map_surjective {X Y} f := by
    let M : StrictPerfectDGComplex A := ForgetEnrichment.to (Complex A) X.as
    let N : ModuleCategory A PUnit.{1} := ForgetEnrichment.of (Complex A) (ringModule A M.val)
    obtain ⟨g, hg⟩ := (moduleProjectiveLocalization_map_bijective A PUnit.{1}
      (P := N) (strictlyPerfectComplex_ringModule_homotopicallyProjective A M.val M.property)
      ((strictPerfectDGComplexToRingModule A).onHomotopy.obj Y)).2 f
    obtain ⟨h, hh⟩ := (strictPerfectDGComplexToRingModule A).onHomotopy.map_surjective g
    refine ⟨h, ?_⟩
    change (moduleHomotopyToDerivedClosed A PUnit.{1}).map
      ((strictPerfectDGComplexToRingModule A).onHomotopy.map h) = f
    rw [hh]
    exact hg

instance strictPerfectDGComplexToDerivedFaithful :
    (strictPerfectDGComplexToDerived A).Faithful where
  map_injective {X Y} f g h := by
    let M : StrictPerfectDGComplex A := ForgetEnrichment.to (Complex A) X.as
    let N : ModuleCategory A PUnit.{1} := ForgetEnrichment.of (Complex A) (ringModule A M.val)
    apply (strictPerfectDGComplexToRingModule A).onHomotopy.map_injective
    exact (moduleProjectiveLocalization_map_bijective A PUnit.{1}
      (P := N) (strictlyPerfectComplex_ringModule_homotopicallyProjective A M.val M.property)
      ((strictPerfectDGComplexToRingModule A).onHomotopy.obj Y)).1 h

end SerrePositivity.DifferentialGraded
end

end StrictComplexDerived

/-! ## StrictComplexDerivedLinear（旧 SerrePositivity/DifferentialGraded/Perfect/StrictComplexDerivedLinear.lean） -/

/-! # 既存PerfectHomotopyから主dg加群導来圏へのA線形完全忠実関手 -/

@[expose] public section StrictComplexDerivedLinear
universe u

noncomputable section
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

instance strictPerfectDGComplexToDerivedAdditive :
    (strictPerfectDGComplexToDerived A).Additive := by
  dsimp [strictPerfectDGComplexToDerived]
  infer_instance

instance strictPerfectDGComplexToDerivedLinear : (strictPerfectDGComplexToDerived A).Linear A := by
  dsimp [strictPerfectDGComplexToDerived]
  infer_instance

/-- 既存PerfectHomotopyを主dg enhancement経由で指定導来圏へ送る。 -/
def perfectHomotopyToDGDerived : PerfectHomotopy A ⥤ DerivedModuleCategory A PUnit.{1} :=
  (strictPerfectDGComplexHomotopyEquivalence A).inverse ⋙ strictPerfectDGComplexToDerived A

instance perfectHomotopyToDGDerivedFull : (perfectHomotopyToDGDerived A).Full := by
  dsimp [perfectHomotopyToDGDerived]
  infer_instance

instance perfectHomotopyToDGDerivedFaithful : (perfectHomotopyToDGDerived A).Faithful := by
  dsimp [perfectHomotopyToDGDerived]
  infer_instance

instance perfectHomotopyToDGDerivedAdditive : (perfectHomotopyToDGDerived A).Additive := by
  dsimp [perfectHomotopyToDGDerived]
  infer_instance

instance perfectHomotopyToDGDerivedLinear : (perfectHomotopyToDGDerived A).Linear A := by
  dsimp [perfectHomotopyToDGDerived]
  infer_instance

/-- 既存perfectへのH⁰比較を経由しても、実際の一対象dg加群による主導来比較と一致する。 -/
def strictPerfectDGComplexToPerfectCompDerived :
    strictPerfectDGComplexToPerfect A ⋙ perfectHomotopyToDGDerived A ≅
      strictPerfectDGComplexToDerived A :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (strictPerfectDGComplexHomotopyEquivalence A).unitIso.symm _ ≪≫
    Functor.leftUnitor _

end SerrePositivity.DifferentialGraded
end

end StrictComplexDerivedLinear

/-! ## StrictComplexOperations（旧 SerrePositivity/DifferentialGraded/Perfect/StrictComplexOperations.lean） -/

/-! # 既存strictlyPerfectComplexの同型・零対象・次数集中に関する補助API -/

@[expose] public section StrictComplexOperations
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 複体の真の同型は有界性と各項の有限射影性を保つ。 -/
lemma strictlyPerfectComplex_of_iso {P Q : Complex A} (e : P ≅ Q)
    (hP : strictlyPerfectComplex A P) : strictlyPerfectComplex A Q := by
  obtain ⟨a, b, ha, hb⟩ := hP.1
  let := ha
  let := hb
  refine ⟨⟨a, b, ?_, ?_⟩, ?_⟩
  · exact (Q.isStrictlyGE_iff a).2 (fun i hi =>
      (P.isZero_of_isStrictlyGE a i hi).of_iso ((eval _ _ i).mapIso e).symm)
  · exact (Q.isStrictlyLE_iff b).2 (fun i hi =>
      (P.isZero_of_isStrictlyLE b i hi).of_iso ((eval _ _ i).mapIso e).symm)
  · intro i
    let := (hP.2 i).1
    let := (hP.2 i).2
    let eX : P.X i ≃ₗ[A] Q.X i := ((eval _ _ i).mapIso e).toLinearEquiv
    exact ⟨Module.Finite.equiv eX, Module.Projective.of_equiv' eX⟩

/-- 零対象と同型な複体も既存の有限射影条件を満たす。 -/
lemma strictlyPerfectComplex_of_isZero (P : Complex A) (hP : IsZero P) :
    strictlyPerfectComplex A P :=
  strictlyPerfectComplex_of_iso A hP.isoZero.symm strictlyPerfectComplex_zero

/-- 任意次数に集中する有限射影加群は既存strictlyPerfectComplexである。 -/
lemma strictlyPerfectComplex_single (M : ModuleCat.{u} A) [Module.Finite A M]
    [Module.Projective A M] (n : ℤ) :
    strictlyPerfectComplex A ((single (ModuleCat.{u} A) (.up ℤ) n).obj M) := by
  refine ⟨⟨n, n, inferInstance, inferInstance⟩, ?_⟩
  intro i
  by_cases hi : i = n
  · subst i
    let e := (singleObjXSelf (.up ℤ) n M).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv' e⟩
  · have hz := isZero_single_obj_X (.up ℤ) n M i hi
    have : Module.Free A (((single (ModuleCat.{u} A) (.up ℤ) n).obj M).X i) :=
      SerrePositivity.isZero_moduleCat_free hz
    exact ⟨SerrePositivity.isZero_moduleCat_finite hz, Module.Projective.of_free⟩

end SerrePositivity.DifferentialGraded
end

end StrictComplexOperations

/-! ## RingBounded（旧 SerrePositivity/DifferentialGraded/Perfect/RingBounded.lean） -/

/-! # 有界有限射影複体の主導来perfect性

下端項への射影の核で有限幅を一つ減らす。短完全列と次数集中複体の比較は既存APIを使う。
-/

@[expose] public section RingBounded
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

/-- 有限の次数範囲にある各項有限射影の複体の主導来像はperfect。 -/
lemma ringComplexDerived_perfect_of_finite_range (w : ℕ) (a : ℤ) (P : Complex A)
    (hterm : ∀ i, Module.Finite A (P.X i) ∧ Module.Projective A (P.X i))
    (hb : ∀ i, (i < a ∨ a + w ≤ i) → IsZero (P.X i)) :
    modulePerfect A PUnit.{1}
      ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P)) := by
  let : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _
  induction w generalizing a P with
  | zero =>
    have hz : IsZero P := by
      rw [IsZero.iff_id_eq_zero]
      apply HomologicalComplex.Hom.ext
      funext i
      exact (hb i (by omega)).eq_of_src _ _
    have hZ := (complexToRingModule A ⋙ moduleToDerived A PUnit.{1}).map_isZero hz
    exact (modulePerfect A PUnit.{1}).prop_of_iso hZ.isoZero.symm
      (modulePerfectOver_zero A PUnit.{1} Set.univ)
  | succ w ih =>
    let ha := fun i (hi : i < a) => hb i (Or.inl hi)
    let π := SerrePositivity.bottomProjection P a ha
    let P' := kernel π
    have : Epi π := SerrePositivity.bottomProjection_epi P a ha
    let S : ShortComplex (Complex A) := ShortComplex.mk (kernel.ι π) π (kernel.condition π)
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel π }
    have hb' : ∀ i, (i < a + 1 ∨ a + 1 + w ≤ i) → IsZero (P'.X i) := by
      intro i hi
      by_cases hia : i = a
      · subst i
        exact SerrePositivity.bottomProjection_kernel_isZero P a ha
      · exact (hb i (by omega)).of_iso
          (SerrePositivity.bottomProjectionKernelXIso P a ha i hia)
    have ht' : ∀ i, Module.Finite A (P'.X i) ∧ Module.Projective A (P'.X i) := by
      intro i
      by_cases hia : i = a
      · subst i
        have hz := SerrePositivity.bottomProjection_kernel_isZero P a ha
        have : Module.Free A (P'.X a) := SerrePositivity.isZero_moduleCat_free hz
        exact ⟨SerrePositivity.isZero_moduleCat_finite hz, Module.Projective.of_free⟩
      · let := (hterm i).1
        let := (hterm i).2
        let e := (SerrePositivity.bottomProjectionKernelXIso P a ha i hia).toLinearEquiv
        exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv' e.symm⟩
    let := (hterm a).1
    let := (hterm a).2
    exact ringComplexDerived_perfect_of_shortExact A S hS (ih (a + 1) P' ht' hb')
      (ringSingleToDerived_finiteProjective_perfect A a (P.X a))

/-- 既存strictlyPerfectComplexの主dg加群導来像は主Perfに入る。 -/
lemma strictlyPerfectComplex_ringDerived_perfect (P : Complex A)
    (hP : strictlyPerfectComplex A P) :
    modulePerfect A PUnit.{1}
      ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P)) := by
  obtain ⟨a, b, ha, hb⟩ := hP.1
  let := ha
  let := hb
  apply ringComplexDerived_perfect_of_finite_range A (b - a + 1).toNat a P hP.2
  intro i hi
  rcases hi with hi | hi
  · exact P.isZero_of_isStrictlyGE a i hi
  · exact P.isZero_of_isStrictlyLE b i (by omega)

end SerrePositivity.DifferentialGraded
end

end RingBounded

/-! ## RingFiniteCell（旧 SerrePositivity/DifferentialGraded/Perfect/RingFiniteCell.lean） -/

/-! # 一対象Aの有限cellの評価は実際の有界有限射影複体

有限操作の木について帰納し、同型操作は真の複体同型として扱う。
-/

@[expose] public section RingFiniteCell
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 一対象A上の有限cellの評価は既存のstrictlyPerfectComplexを満たす。 -/
lemma moduleFiniteCell_ringEvaluation_strictlyPerfect {S : Set PUnit.{1}}
    {M : ModuleCategory A PUnit.{1}} (hM : moduleFiniteCellOver A PUnit.{1} S M) :
    strictlyPerfectComplex A ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M) := by
  obtain ⟨c⟩ := hM
  induction c with
  | zero =>
    exact strictlyPerfectComplex_of_isZero A _
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map_isZero (moduleZero_isZero A PUnit.{1}))
  | generator x hx =>
    cases x
    exact strictlyPerfectComplex_single A (ModuleCat.of A A) 0
  | shift s c ih => exact strictlyPerfectComplex_shift ih s
  | sum c d ihc ihd => exact strictlyPerfectComplex_biprod ihc ihd
  | cone c d f ihc ihd =>
    exact strictlyPerfectComplex_mappingCone A
      ((moduleEvaluation A PUnit.{1} PUnit.unit).map f) ihc ihd
  | iso c e ih =>
    exact strictlyPerfectComplex_of_iso A ((moduleEvaluation A PUnit.{1} PUnit.unit).mapIso e) ih

end SerrePositivity.DifferentialGraded
end

end RingFiniteCell

/-! ## RingEnhancement（旧 SerrePositivity/DifferentialGraded/Perfect/RingEnhancement.lean） -/

/-! # 有限射影複体から主perfect dg enhancementへの実際のdg関手 -/

@[expose] public section RingEnhancement
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 有限射影複体の定数加群は主射影的perfect条件を満たす。 -/
lemma strictlyPerfectComplex_ringModule_perfectProjective (P : Complex A)
    (hP : strictlyPerfectComplex A P) :
    modulePerfectProjectiveOver A PUnit.{1} Set.univ (ringModule A P) :=
  ⟨strictlyPerfectComplex_ringModule_homotopicallyProjective A P hP,
    strictlyPerfectComplex_ringDerived_perfect A P hP⟩

/-- 対象を実際のringModuleへ、全Homを評価同型の逆へ送るdg比較。 -/
def strictPerfectDGComplexToPerfectDG :
    DGFunctor A (StrictPerfectDGComplex A) (PerfectDGModule A PUnit.{1}) :=
  (ringConstantDG A).restrict (strictlyPerfectComplex A)
    (modulePerfectProjectiveOver A PUnit.{1} Set.univ)
    (strictlyPerfectComplex_ringModule_perfectProjective A)

/-- 主dg包含との比較は元の全一対象加群へのdg関手との等式。 -/
lemma strictPerfectDGComplexToPerfectDG_comp_inclusion :
    DGFunctor.comp (strictPerfectDGComplexToPerfectDG A)
      (perfectDGModuleInclusion A PUnit.{1} Set.univ) =
    DGFunctor.comp (strictPerfectDGComplexInclusion A) (ringConstantDG A) :=
  (ringConstantDG A).restrict_comp_inclusion (strictlyPerfectComplex A)
    (modulePerfectProjectiveOver A PUnit.{1} Set.univ)
    (strictlyPerfectComplex_ringModule_perfectProjective A)

instance strictPerfectDGComplexToPerfectDGHomotopyFull :
    (strictPerfectDGComplexToPerfectDG A).onHomotopy.Full :=
  (strictPerfectDGComplexToPerfectDG A).onHomotopy_full_of_homIso (fun P N => by
    change IsIso (ringConstantHomIso A P.val N.val).inv
    infer_instance)

instance strictPerfectDGComplexToPerfectDGHomotopyFaithful :
    (strictPerfectDGComplexToPerfectDG A).onHomotopy.Faithful :=
  (strictPerfectDGComplexToPerfectDG A).onHomotopy_faithful_of_homIso (fun P N => by
    change IsIso (ringConstantHomIso A P.val N.val).inv
    infer_instance)

end SerrePositivity.DifferentialGraded
end

end RingEnhancement

/-! ## RingFiniteCellImage（旧 SerrePositivity/DifferentialGraded/Perfect/RingFiniteCellImage.lean） -/

/-! # 一対象Aの有限cellは有限射影dg複体比較のH⁰本質像に入る -/

@[expose] public section RingFiniteCellImage
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A]

/-- 実際の有限cell代表を持つ主perfect dg対象は、有限射影複体の比較の像となる。 -/
lemma strictPerfectDGComplexToPerfectDG_essImage_of_finiteCell
    (X : HomotopyCategory A (PerfectDGModule A PUnit.{1}))
    (hX : moduleFiniteCell A PUnit.{1}
      (ForgetEnrichment.of (Complex A)
        (ForgetEnrichment.to (Complex A) X.as).val)) :
    (strictPerfectDGComplexToPerfectDG A).onHomotopy.essImage X := by
  let M : PerfectDGModule A PUnit.{1} := ForgetEnrichment.to (Complex A) X.as
  let P : Complex A := M.val.obj (op PUnit.unit)
  have hP : strictlyPerfectComplex A P := moduleFiniteCell_ringEvaluation_strictlyPerfect A hX
  refine ⟨(toHomotopy A (StrictPerfectDGComplex A)).obj
    (ForgetEnrichment.of (Complex A) ⟨P, hP⟩), ⟨eqToIso ?_⟩⟩
  change (toHomotopy A (PerfectDGModule A PUnit.{1})).obj
      (ForgetEnrichment.of (Complex A) ((strictPerfectDGComplexToPerfectDG A).obj ⟨P, hP⟩)) =
    (toHomotopy A (PerfectDGModule A PUnit.{1})).obj (ForgetEnrichment.of (Complex A) M)
  apply congrArg (fun Y : PerfectDGModule A PUnit.{1} =>
    (toHomotopy A (PerfectDGModule A PUnit.{1})).obj (ForgetEnrichment.of (Complex A) Y))
  apply Subtype.ext
  exact ringModule_recover A M.val

end SerrePositivity.DifferentialGraded
end

end RingFiniteCellImage

/-! ## RingPerfectComparison（旧 SerrePositivity/DifferentialGraded/Perfect/RingPerfectComparison.lean） -/

/-! # 既存PerfectHomotopyから主PerfへのA線形完全忠実比較

実際のdg比較をH⁰へ降ろし、主射影的enhancementとPerfの既存同値を合成する。
-/

@[expose] public section RingPerfectComparison
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]

/-- 有限射影dg複体のH⁰から主Perfへの実際のdg比較に基づく関手。 -/
def strictPerfectDGComplexToDGPerfect : HomotopyCategory A (StrictPerfectDGComplex A) ⥤
    PerfectModuleCategory A PUnit.{1} :=
  (strictPerfectDGComplexToPerfectDG A).onHomotopy ⋙
    perfectDGModuleToPerfect A PUnit.{1} Set.univ

instance strictPerfectDGComplexToDGPerfectFull : (strictPerfectDGComplexToDGPerfect A).Full := by
  dsimp [strictPerfectDGComplexToDGPerfect]
  infer_instance

instance strictPerfectDGComplexToDGPerfectFaithful :
    (strictPerfectDGComplexToDGPerfect A).Faithful := by
  dsimp [strictPerfectDGComplexToDGPerfect]
  infer_instance

instance strictPerfectDGComplexToDGPerfectAdditive :
    (strictPerfectDGComplexToDGPerfect A).Additive := by
  dsimp [strictPerfectDGComplexToDGPerfect]
  infer_instance

instance strictPerfectDGComplexToDGPerfectLinear :
    (strictPerfectDGComplexToDGPerfect A).Linear A := by
  dsimp [strictPerfectDGComplexToDGPerfect]
  infer_instance

/-- dg包含の可換性をH⁰と主局所化へ送り、既存の主導来比較と照合する。 -/
def strictPerfectDGComplexToPerfectDGCompDerived :
    (strictPerfectDGComplexToPerfectDG A).onHomotopy ⋙
      perfectDGModuleToDerived A PUnit.{1} Set.univ ≅ strictPerfectDGComplexToDerived A := by
  have h : (strictPerfectDGComplexToPerfectDG A).onHomotopy ⋙
      (perfectDGModuleInclusion A PUnit.{1} Set.univ).onHomotopy =
      (strictPerfectDGComplexToRingModule A).onHomotopy :=
    (DGFunctor.onHomotopy_comp (strictPerfectDGComplexToPerfectDG A)
      (perfectDGModuleInclusion A PUnit.{1} Set.univ)).symm.trans
      (congrArg (fun F => DGFunctor.onHomotopy F)
        (strictPerfectDGComplexToPerfectDG_comp_inclusion A))
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (eqToIso h) (moduleHomotopyToDerivedClosed A PUnit.{1})

/-- 主Perf包含を経由しても、同じ有限射影複体の主導来像となる。 -/
def strictPerfectDGComplexToDGPerfectCompInclusion :
    strictPerfectDGComplexToDGPerfect A ⋙ perfectModuleInclusion A PUnit.{1} Set.univ ≅
      strictPerfectDGComplexToDerived A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (strictPerfectDGComplexToPerfectDG A).onHomotopy
      (perfectDGModuleToPerfectCompInclusion A PUnit.{1} Set.univ) ≪≫
    strictPerfectDGComplexToPerfectDGCompDerived A

/-- 既存PerfectHomotopyから主PerfへのA線形比較。 -/
def perfectHomotopyToDGPerfect : PerfectHomotopy A ⥤ PerfectModuleCategory A PUnit.{1} :=
  (strictPerfectDGComplexHomotopyEquivalence A).inverse ⋙ strictPerfectDGComplexToDGPerfect A

instance perfectHomotopyToDGPerfectFull : (perfectHomotopyToDGPerfect A).Full := by
  dsimp [perfectHomotopyToDGPerfect]
  infer_instance

instance perfectHomotopyToDGPerfectFaithful : (perfectHomotopyToDGPerfect A).Faithful := by
  dsimp [perfectHomotopyToDGPerfect]
  infer_instance

instance perfectHomotopyToDGPerfectAdditive : (perfectHomotopyToDGPerfect A).Additive := by
  dsimp [perfectHomotopyToDGPerfect]
  infer_instance

instance perfectHomotopyToDGPerfectLinear : (perfectHomotopyToDGPerfect A).Linear A := by
  dsimp [perfectHomotopyToDGPerfect]
  infer_instance

/-- 既存PerfectHomotopyからの主導来比較は主Perf包含を通して自然に因子化する。 -/
def perfectHomotopyToDGPerfectCompInclusion :
    perfectHomotopyToDGPerfect A ⋙ perfectModuleInclusion A PUnit.{1} Set.univ ≅
      perfectHomotopyToDGDerived A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (strictPerfectDGComplexHomotopyEquivalence A).inverse
      (strictPerfectDGComplexToDGPerfectCompInclusion A)

end SerrePositivity.DifferentialGraded
end

end RingPerfectComparison

/-! ## RingPerfectTriangulated（旧 SerrePositivity/DifferentialGraded/Perfect/RingPerfectTriangulated.lean） -/

/-! # 既存PerfectHomotopyから主Perfへの比較のshift・三角整合性

既存の通常Qhを通る比較との自然同型で構造を運び、主Perf包含で反映する。
-/

@[expose] public section RingPerfectTriangulated
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A]
local instance : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

local instance : (perfectModuleInclusion A PUnit.{1} Set.univ).Full := by
  dsimp [perfectModuleInclusion]
  infer_instance

local instance : (perfectModuleInclusion A PUnit.{1} Set.univ).Faithful := by
  dsimp [perfectModuleInclusion]
  infer_instance

/-- 有限射影dg複体の主導来比較と既存Qhによる比較の自然同型。 -/
def strictPerfectDGComplexDerivedCanonicalIso :
    strictPerfectDGComplexToDerived A ≅ strictPerfectDGComplexToHomotopy A ⋙
      DerivedCategory.Qh ⋙ (ringDerivedEquivalence A).inverse :=
  Functor.isoWhiskerRight
      (eqToIso (DGFunctor.onHomotopy_comp (strictPerfectDGComplexInclusion A)
        (ringConstantDG A))) (moduleHomotopyToDerivedClosed A PUnit.{1}) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (strictPerfectDGComplexInclusion A).onHomotopy
      (complexHomotopyRingDerivedIso A) ≪≫
    (Functor.associator _ _ _).symm

/-- 既存PerfectHomotopyからの主導来比較を、元の包含・Qhと同定する。 -/
def perfectHomotopyToDGDerivedCanonicalIso :
    perfectHomotopyToDGDerived A ≅ perfectHomotopyInclusion A ⋙
      DerivedCategory.Qh ⋙ (ringDerivedEquivalence A).inverse := by
  let E := strictPerfectDGComplexHomotopyEquivalence A
  let I := perfectHomotopyInclusion A
  let h : E.inverse ⋙ strictPerfectDGComplexToHomotopy A ≅ I :=
    Functor.isoWhiskerLeft E.inverse (strictPerfectDGComplexToPerfectCompInclusion A).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight E.counitIso I ≪≫ Functor.leftUnitor I
  exact Functor.isoWhiskerLeft E.inverse (strictPerfectDGComplexDerivedCanonicalIso A) ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight h _

instance perfectHomotopyToDGDerivedCommShift : (perfectHomotopyToDGDerived A).CommShift ℤ :=
  Functor.CommShift.ofIso (perfectHomotopyToDGDerivedCanonicalIso A).symm ℤ

instance perfectHomotopyToDGDerivedCanonicalIsoCommShift :
    NatTrans.CommShift (perfectHomotopyToDGDerivedCanonicalIso A).hom ℤ := by
  have : NatTrans.CommShift (perfectHomotopyToDGDerivedCanonicalIso A).symm.hom ℤ :=
    Functor.CommShift.ofIso_compatibility (perfectHomotopyToDGDerivedCanonicalIso A).symm ℤ
  exact NatTrans.CommShift.of_iso_inv (perfectHomotopyToDGDerivedCanonicalIso A).symm ℤ

instance perfectHomotopyToDGDerivedIsTriangulated :
    (perfectHomotopyToDGDerived A).IsTriangulated :=
  Functor.isTriangulated_of_iso (perfectHomotopyToDGDerivedCanonicalIso A).symm

instance perfectHomotopyToDGPerfectCommShift : (perfectHomotopyToDGPerfect A).CommShift ℤ :=
  Functor.CommShift.ofComp (perfectHomotopyToDGPerfectCompInclusion A) ℤ

instance perfectHomotopyToDGPerfectCompInclusionCommShift :
    NatTrans.CommShift (perfectHomotopyToDGPerfectCompInclusion A).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (perfectHomotopyToDGPerfectCompInclusion A) ℤ

instance perfectHomotopyToDGPerfectIsTriangulated :
    (perfectHomotopyToDGPerfect A).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (perfectHomotopyToDGPerfectCompInclusion A)).2
    inferInstance

end SerrePositivity.DifferentialGraded
end

end RingPerfectTriangulated

/-! ## RingRetract（旧 SerrePositivity/DifferentialGraded/Perfect/RingRetract.lean） -/

/-! # 主Perfの対象は既存有限射影ホモトピー圏の比較像のretract

finite cellの実際の評価複体を使ってretractの上の対象を既存PerfectHomotopyで表す。
-/

@[expose] public section RingRetract
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]
local instance : HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

/-- 一対象Aの有限cellの評価を既存PerfectHomotopyの実際の対象にする。 -/
def ringFiniteCellPerfectHomotopy (M : ModuleCategory A PUnit.{1})
    (hM : moduleFiniteCell A PUnit.{1} M) : PerfectHomotopy A :=
  ⟨(_root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)).obj
      ((moduleEvaluation A PUnit.{1} PUnit.unit).obj M),
    (perfectHomotopyProperty_quotient A _).2
      (moduleFiniteCell_ringEvaluation_strictlyPerfect A hM)⟩

/-- この既存有限射影対象の主導来比較は、元の有限cellの主局所化像と同型。 -/
def ringFiniteCellPerfectHomotopyDerivedIso (M : ModuleCategory A PUnit.{1})
    (hM : moduleFiniteCell A PUnit.{1} M) :
    (perfectHomotopyToDGDerived A).obj (ringFiniteCellPerfectHomotopy A M hM) ≅
      (moduleToDerived A PUnit.{1}).obj M := by
  let P : Complex A := (moduleEvaluation A PUnit.{1} PUnit.unit).obj M
  let e : (moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P) ≅
      (moduleToDerived A PUnit.{1}).obj M := eqToIso (congrArg
    (fun N => (moduleToDerived A PUnit.{1}).obj (ForgetEnrichment.of (Complex A) N))
      (ringModule_recover A (ForgetEnrichment.to (Complex A) M)))
  exact (perfectHomotopyToDGDerivedCanonicalIso A).app (ringFiniteCellPerfectHomotopy A M hM) ≪≫
    (ringDerivedEquivalence A).inverse.mapIso
      ((DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)).app P) ≪≫
    ringComplexDerivedUnitIso A P ≪≫ e

/-- 主Perfの全対象は、既存PerfectHomotopyからの実際の比較像のretractである。 -/
lemma perfectModule_ring_retract_of_perfectHomotopy (X : PerfectModuleCategory A PUnit.{1}) :
    ∃ P : PerfectHomotopy A, Nonempty (Retract X ((perfectHomotopyToDGPerfect A).obj P)) := by
  obtain ⟨M, hM, ⟨r⟩⟩ := (modulePerfect_iff A PUnit.{1} X.obj).1 X.property
  let P := ringFiniteCellPerfectHomotopy A M hM
  let e : ((perfectHomotopyToDGPerfect A).obj P).obj ≅
      (moduleToDerived A PUnit.{1}).obj M :=
    (perfectHomotopyToDGPerfectCompInclusion A).app P ≪≫
      ringFiniteCellPerfectHomotopyDerivedIso A M hM
  let r' := r.trans (Retract.ofIso e.symm)
  refine ⟨P, ⟨{ i := ObjectProperty.homMk r'.i
                r := ObjectProperty.homMk r'.r
                retract := ?_ }⟩⟩
  exact (modulePerfect A PUnit.{1}).hom_ext r'.retract

end SerrePositivity.DifferentialGraded
end

end RingRetract

/-! ## RingRetractTopHomology（旧 SerrePositivity/DifferentialGraded/Perfect/RingRetractTopHomology.lean） -/

/-! # 有界有限射影複体の導来retractの最上ホモロジー

上端ではcyclesが項そのものなので有限生成性を使える。一般の次数のホモロジーに
有限生成性を仮定するものではなく、Noetherian性・coherent性は不要。
-/

@[expose] public section RingRetractTopHomology
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A]

lemma finiteModule_of_retract {M N : ModuleCat.{u} A} (a : Retract M N) [Module.Finite A N] :
    Module.Finite A M :=
  Module.Finite.of_surjective a.r.hom (fun x =>
    ⟨a.i.hom x, congrArg (fun f => f.hom x) a.retract⟩)

lemma ringComplex_topHomology_finite (P : Complex A) (n : ℤ)
    [Module.Finite A (P.X n)] (hd : P.d n (n + 1) = 0) :
    Module.Finite A (P.homology n) := by
  let e := P.iCyclesIso n (n + 1) (by simp) hd
  let : Module.Finite A (P.cycles n) := Module.Finite.equiv e.toLinearEquiv.symm
  exact Module.Finite.of_surjective (P.homologyπ n).hom
    ((ModuleCat.epi_iff_surjective (P.homologyπ n)).1 inferInstance)

def ringComplexDerivedHomologyIso (P : Complex A) (n : ℤ) :
    (moduleDerivedHomology A PUnit.{1} PUnit.unit n).obj
        ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P)) ≅ P.homology n :=
  eqToIso (congrArg (fun F => F.obj ((complexToRingModule A).obj P))
    (moduleDerivedHomology_fac A PUnit.{1} PUnit.unit n)) ≪≫
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) n).mapIso
        ((complexToRingModuleEvaluationIso A).app P)

lemma ringDerivedRetract_topHomology_finite (P : Complex A) (n : ℤ)
    [Module.Finite A (P.X n)] (hd : P.d n (n + 1) = 0)
    {X : DerivedModuleCategory A PUnit.{1}}
    (a : Retract X ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P))) :
    Module.Finite A ((moduleDerivedHomology A PUnit.{1} PUnit.unit n).obj X) := by
  let := ringComplex_topHomology_finite A P n hd
  exact finiteModule_of_retract A
    ((a.map (moduleDerivedHomology A PUnit.{1} PUnit.unit n)).trans
      (Retract.ofIso (ringComplexDerivedHomologyIso A P n)))

lemma ringDerivedRetract_topHomology_finite_of_strictlyPerfect (P : Complex A)
    (hP : strictlyPerfectComplex A P) (n : ℤ) [P.IsStrictlyLE n]
    {X : DerivedModuleCategory A PUnit.{1}}
    (a : Retract X ((moduleToDerived A PUnit.{1}).obj ((complexToRingModule A).obj P))) :
    Module.Finite A ((moduleDerivedHomology A PUnit.{1} PUnit.unit n).obj X) := by
  let := (hP.2 n).1
  exact ringDerivedRetract_topHomology_finite A P n
    ((P.isZero_of_isStrictlyLE n (n + 1) (by omega)).eq_of_tgt _ _) a

end SerrePositivity.DifferentialGraded
end

end RingRetractTopHomology

/-! ## RingKaroubi（旧 SerrePositivity/DifferentialGraded/Perfect/RingKaroubi.lean） -/

/-! # 既存PerfectHomotopyのKaroubi包絡と主Perfの比較

元のPerfectHomotopyの冪等完備性を仮定せず、形式的retractを主Perfで実現する。
-/

@[expose] public section RingKaroubi
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory CategoryTheory.Idempotents
variable (A : Type u) [CommRing A]

/-- 既存有限射影比較の、両辺のKaroubi包絡への実際の延長。 -/
def ringPerfectKaroubiFunctor : Karoubi (PerfectHomotopy A) ⥤
    Karoubi (PerfectModuleCategory A PUnit.{1}) :=
  (functorExtension₂ _ _).obj (perfectHomotopyToDGPerfect A)

instance ringPerfectKaroubiFunctorFull : (ringPerfectKaroubiFunctor A).Full := by
  dsimp [ringPerfectKaroubiFunctor]
  infer_instance

instance ringPerfectKaroubiFunctorFaithful : (ringPerfectKaroubiFunctor A).Faithful := by
  dsimp [ringPerfectKaroubiFunctor]
  infer_instance

instance ringPerfectKaroubiFunctorEssSurj : (ringPerfectKaroubiFunctor A).EssSurj where
  mem_essImage X := by
    obtain ⟨P, ⟨r⟩⟩ := perfectModule_ring_retract_of_perfectHomotopy A X.X
    exact karoubiExtension_mem_essImage (perfectHomotopyToDGPerfect A) X P
      ((karoubiRetract X).trans (r.map (toKaroubi (PerfectModuleCategory A PUnit.{1}))))

instance ringPerfectKaroubiFunctorIsEquivalence : (ringPerfectKaroubiFunctor A).IsEquivalence where

instance ringPerfectKaroubiFunctorAdditive : (ringPerfectKaroubiFunctor A).Additive := by
  dsimp [ringPerfectKaroubiFunctor]
  infer_instance

instance ringPerfectKaroubiFunctorLinear : (ringPerfectKaroubiFunctor A).Linear A := by
  dsimp [ringPerfectKaroubiFunctor]
  infer_instance

instance ringPerfectKaroubiFunctorCommShift : (ringPerfectKaroubiFunctor A).CommShift ℤ := by
  dsimp [ringPerfectKaroubiFunctor]
  infer_instance

instance ringPerfectKaroubiFunctorIsTriangulated :
    (ringPerfectKaroubiFunctor A).IsTriangulated := by
  dsimp [ringPerfectKaroubiFunctor]
  infer_instance

/-- 主Perfの既存冪等完備性を使い、形式的retractを実際のperfect対象として実現する。 -/
def ringPerfectKaroubiRealization :
    Karoubi (PerfectHomotopy A) ⥤ PerfectModuleCategory A PUnit.{1} :=
  (functorExtension _ _).obj (perfectHomotopyToDGPerfect A)

instance ringPerfectKaroubiRealizationIsEquivalence :
    (ringPerfectKaroubiRealization A).IsEquivalence := by
  change (ringPerfectKaroubiFunctor A ⋙
    (toKaroubiEquivalence (PerfectModuleCategory A PUnit.{1})).inverse).IsEquivalence
  infer_instance

instance ringPerfectKaroubiRealizationAdditive : (ringPerfectKaroubiRealization A).Additive := by
  dsimp [ringPerfectKaroubiRealization]
  infer_instance

instance ringPerfectKaroubiRealizationLinear : (ringPerfectKaroubiRealization A).Linear A := by
  let E := toKaroubiEquivalence (PerfectModuleCategory A PUnit.{1})
  have : E.functor.Linear A := by
    change (toKaroubi (PerfectModuleCategory A PUnit.{1})).Linear A
    infer_instance
  have : E.inverse.Linear A := inferInstance
  change (ringPerfectKaroubiFunctor A ⋙ E.inverse).Linear A
  infer_instance

/-- 実現して再びKaroubiへ入れる経路は、元のKaroubi延長と一致する。 -/
def ringPerfectKaroubiRealizationToKaroubiIso :
    ringPerfectKaroubiRealization A ⋙ toKaroubi (PerfectModuleCategory A PUnit.{1}) ≅
      ringPerfectKaroubiFunctor A :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (ringPerfectKaroubiFunctor A)
      (toKaroubiEquivalence (PerfectModuleCategory A PUnit.{1})).counitIso ≪≫
    Functor.rightUnitor _

instance ringPerfectKaroubiRealizationCommShift :
    (ringPerfectKaroubiRealization A).CommShift ℤ :=
  Functor.CommShift.ofComp (ringPerfectKaroubiRealizationToKaroubiIso A) ℤ

instance ringPerfectKaroubiRealizationToKaroubiIsoCommShift :
    NatTrans.CommShift (ringPerfectKaroubiRealizationToKaroubiIso A).hom ℤ :=
  Functor.CommShift.ofComp_compatibility (ringPerfectKaroubiRealizationToKaroubiIso A) ℤ

instance ringPerfectKaroubiRealizationIsTriangulated :
    (ringPerfectKaroubiRealization A).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (ringPerfectKaroubiRealizationToKaroubiIso A)).2
    inferInstance

/-- 実現は元の有限射影ホモトピー圏上では既存の実際の比較に一致する。 -/
def ringPerfectKaroubiRealization_fac :
    toKaroubi (PerfectHomotopy A) ⋙ ringPerfectKaroubiRealization A ≅
      perfectHomotopyToDGPerfect A :=
  karoubiExtensionToCompleteFactors (perfectHomotopyToDGPerfect A)

/-- 既存有限射影ホモトピー圏のKaroubi包絡と主Perfとの実際の同値。 -/
def ringPerfectKaroubiEquivalence :
    Karoubi (PerfectHomotopy A) ≌ PerfectModuleCategory A PUnit.{1} :=
  (ringPerfectKaroubiRealization A).asEquivalence

instance ringPerfectKaroubiEquivalenceFunctorLinear :
    (ringPerfectKaroubiEquivalence A).functor.Linear A := ringPerfectKaroubiRealizationLinear A

instance ringPerfectKaroubiEquivalenceFunctorAdditive :
    (ringPerfectKaroubiEquivalence A).functor.Additive := ringPerfectKaroubiRealizationAdditive A

instance ringPerfectKaroubiEquivalenceFunctorCommShift :
    (ringPerfectKaroubiEquivalence A).functor.CommShift ℤ :=
  ringPerfectKaroubiRealizationCommShift A

instance ringPerfectKaroubiEquivalenceInverseCommShift :
    (ringPerfectKaroubiEquivalence A).inverse.CommShift ℤ :=
  (ringPerfectKaroubiEquivalence A).commShiftInverse ℤ

instance ringPerfectKaroubiEquivalenceCommShift : (ringPerfectKaroubiEquivalence A).CommShift ℤ :=
  (ringPerfectKaroubiEquivalence A).commShift_of_functor ℤ

instance ringPerfectKaroubiEquivalenceIsTriangulated :
    (ringPerfectKaroubiEquivalence A).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ (ringPerfectKaroubiRealizationIsTriangulated A)

end SerrePositivity.DifferentialGraded
end

end RingKaroubi

/-! ## RingFiniteHomologyCover（旧 SerrePositivity/DifferentialGraded/Perfect/RingFiniteHomologyCover.lean） -/

/-! # 有限生成ホモロジーの有限自由singleによる被覆

有限自由加群からホモロジーへの全射をcyclesへ持ち上げ、実際のchain mapを構成する。
-/

@[expose] public section RingFiniteHomologyCover
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

def ringSingleMapOfCycles (P : Complex A) (n : ℤ) {F : ModuleCat.{u} A}
    (q : F ⟶ P.cycles n) : (single (ModuleCat.{u} A) (.up ℤ) n).obj F ⟶ P :=
  mkHomFromSingle (q ≫ P.iCycles n) (fun k _ => by
    rw [Category.assoc, P.iCycles_d, comp_zero])

lemma ringSingleMapOfCycles_cycles (P : Complex A) (n : ℤ) {F : ModuleCat.{u} A}
    (q : F ⟶ P.cycles n) :
    (singleObjCyclesSelfIso (.up ℤ) n F).inv ≫
      cyclesMap (ringSingleMapOfCycles A P n q) n = q := by
  apply (cancel_mono (P.iCycles n)).1
  rw [Category.assoc, cyclesMap_i, ← Category.assoc, singleObjCyclesSelfIso_inv_iCycles,
    ringSingleMapOfCycles, mkHomFromSingle_f]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

lemma ringSingleMapOfCycles_homology_epi (P : Complex A) (n : ℤ) {F : ModuleCat.{u} A}
    (q : F ⟶ P.cycles n) [Epi (q ≫ P.homologyπ n)] :
    Epi (homologyMap (ringSingleMapOfCycles A P n q) n) := by
  let S := (single (ModuleCat.{u} A) (.up ℤ) n).obj F
  let k := (singleObjCyclesSelfIso (.up ℤ) n F).inv ≫ S.homologyπ n
  have h : k ≫ homologyMap (ringSingleMapOfCycles A P n q) n = q ≫ P.homologyπ n := by
    dsimp only [k]
    rw [Category.assoc, homologyπ_naturality, ← Category.assoc,
      ringSingleMapOfCycles_cycles A P n q]
  have : Epi (k ≫ homologyMap (ringSingleMapOfCycles A P n q) n) := by
    rw [h]
    infer_instance
  exact epi_of_epi k _

lemma ringComplex_exists_finiteFree_homologyCover (P : Complex A) (n : ℤ)
    [Module.Finite A (P.homology n)] :
    ∃ (m : ℕ) (f : (single (ModuleCat.{u} A) (.up ℤ) n).obj
        (ModuleCat.of A (Fin m → A)) ⟶ P), Epi (homologyMap f n) := by
  obtain ⟨m, g, hg⟩ := Module.Finite.exists_fin' A (P.homology n)
  let F := ModuleCat.of A (Fin m → A)
  let g' : F ⟶ P.homology n := ModuleCat.ofHom g
  have : Epi g' := (ModuleCat.epi_iff_surjective g').2 hg
  let q := Projective.factorThru g' (P.homologyπ n)
  have : Epi (q ≫ P.homologyπ n) := by
    change Epi (Projective.factorThru g' (P.homologyπ n) ≫ P.homologyπ n)
    rw [Projective.factorThru_comp]
    infer_instance
  exact ⟨m, ringSingleMapOfCycles A P n q, ringSingleMapOfCycles_homology_epi A P n q⟩

end SerrePositivity.DifferentialGraded
end

end RingFiniteHomologyCover

/-! ## RingTopTruncation（旧 SerrePositivity/DifferentialGraded/Perfect/RingTopTruncation.lean） -/

/-! # 射影的上端を取り除く良い切断

上端の微分が全射なら、その核は有限射影項の直和因子である。
良い切断により一段短い有限射影複体を得る。
-/

@[expose] public section RingTopTruncation
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

lemma ringComplex_cycles_finite_projective_of_epi (P : Complex A) (n : ℤ)
    [Module.Finite A (P.X n)] [Module.Projective A (P.X n)]
    [Module.Projective A (P.X (n + 1))] [Epi (P.d n (n + 1))] :
    Module.Finite A (P.cycles n) ∧ Module.Projective A (P.cycles n) := by
  let d := P.d n (n + 1)
  let s := Projective.factorThru (𝟙 (P.X (n + 1))) d
  have hs : s ≫ d = 𝟙 _ := Projective.factorThru_comp _ _
  let q := P.liftCycles (𝟙 (P.X n) - d ≫ s) (n + 1) (by simp) (by
    change (𝟙 (P.X n) - d ≫ s) ≫ d = 0
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, hs, Category.comp_id, sub_self])
  have hq : P.iCycles n ≫ q = 𝟙 _ := by
    apply (cancel_mono (P.iCycles n)).1
    rw [Category.assoc, liftCycles_i, Category.id_comp, Preadditive.comp_sub,
      Category.comp_id, ← Category.assoc]
    have h : P.iCycles n ≫ d = 0 := P.iCycles_d n (n + 1)
    rw [h, zero_comp, sub_zero]
  let a : Retract (P.cycles n) (P.X n) := ⟨P.iCycles n, q, hq⟩
  exact ⟨finiteModule_of_retract A a,
    Module.Projective.of_split (P.iCycles n).hom q.hom (congrArg (fun f => f.hom) hq)⟩

lemma ringComplex_truncLE_strictlyGE (P : Complex A) (a n : ℤ) (han : a ≤ n)
    [P.IsStrictlyGE a] : (P.truncLE n).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  exact (P.isZero_of_isStrictlyGE a i hi).of_iso (P.truncLEXIso n i (by omega))

lemma ringComplex_truncLE_strictlyPerfect_of_epi (P : Complex A)
    (hP : strictlyPerfectComplex A P) (n : ℤ) [Epi (P.d n (n + 1))] :
    strictlyPerfectComplex A (P.truncLE n) := by
  obtain ⟨a, b, ha, hb⟩ := hP.1
  let := ha
  let := hb
  have : P.IsStrictlyGE (min a n) := P.isStrictlyGE_of_ge (min a n) a (min_le_left _ _)
  have : (P.truncLE n).IsStrictlyGE (min a n) :=
    ringComplex_truncLE_strictlyGE A P (min a n) n (min_le_right _ _)
  refine ⟨⟨min a n, n, inferInstance, inferInstance⟩, fun i => ?_⟩
  rcases lt_trichotomy i n with hi | hi | hi
  · let := (hP.2 i).1
    let := (hP.2 i).2
    let e := (P.truncLEXIso n i hi).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv' e⟩
  · subst i
    let := (hP.2 n).1
    let := (hP.2 n).2
    let := (hP.2 (n + 1)).2
    obtain ⟨hf, hp⟩ := ringComplex_cycles_finite_projective_of_epi A P n
    let := hf
    let := hp
    let e := (P.truncLEXIsoCycles n).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv' e⟩
  · have hz := (P.truncLE n).isZero_of_isStrictlyLE n i hi
    have : Module.Free A ((P.truncLE n).X i) := SerrePositivity.isZero_moduleCat_free hz
    exact ⟨SerrePositivity.isZero_moduleCat_finite hz, Module.Projective.of_free⟩

lemma ringComplex_truncLE_quasiIso_of_top_exact (P : Complex A) (n : ℤ)
    [P.IsStrictlyLE (n + 1)] (h : P.ExactAt (n + 1)) : QuasiIso (P.ιTruncLE n) := by
  have : P.IsLE n := by
    rw [CochainComplex.isLE_iff]
    intro i hi
    by_cases he : i = n + 1
    · simpa only [he] using h
    · exact P.exactAt_of_isLE (n + 1) i (by omega)
  infer_instance

lemma ringComplex_d_epi_of_top_exact (P : Complex A) (n : ℤ)
    [P.IsStrictlyLE (n + 1)] (h : P.ExactAt (n + 1)) : Epi (P.d n (n + 1)) := by
  have h' : (P.sc' n (n + 1) (n + 2)).Exact :=
    (P.exactAt_iff' n (n + 1) (n + 2) (by simp) (by simp; omega)).1 h
  exact h'.epi_f ((P.isZero_of_isStrictlyLE (n + 1) (n + 2) (by omega)).eq_of_tgt _ _)

lemma ringComplex_topTruncation (P : Complex A) (hP : strictlyPerfectComplex A P) (n : ℤ)
    [P.IsStrictlyLE (n + 1)] (h : P.ExactAt (n + 1)) :
    strictlyPerfectComplex A (P.truncLE n) ∧ QuasiIso (P.ιTruncLE n) := by
  let := ringComplex_d_epi_of_top_exact A P n h
  exact ⟨ringComplex_truncLE_strictlyPerfect_of_epi A P hP n,
    ringComplex_truncLE_quasiIso_of_top_exact A P n h⟩

end SerrePositivity.DifferentialGraded
end

end RingTopTruncation

/-! ## RingHomologyCoverCone（旧 SerrePositivity/DifferentialGraded/Perfect/RingHomologyCoverCone.lean） -/

/-! # 有限射影singleによる上端被覆のconeを一段短くする

次数幅の帰納法で用いる、実際の有限射影複体上の操作。
-/

@[expose] public section RingHomologyCoverCone
universe u

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A]

lemma ringComplex_coverCone_topExact {F P : Complex A} (f : F ⟶ P) (b : ℤ)
    [Epi (homologyMap f b)] (hF : IsZero (F.homology (b + 1))) :
    (CochainComplex.mappingCone f).ExactAt b := by
  have hg : homologyMap (CochainComplex.mappingCone.inr f) b = 0 :=
    (Cone.exact₂ f b).epi_f_iff.1 inferInstance
  have : Mono (Cone.δ f b (b + 1) rfl) := (Cone.exact₃ f b (b + 1) rfl).mono_g hg
  rw [exactAt_iff_isZero_homology, IsZero.iff_id_eq_zero]
  apply (cancel_mono (Cone.δ f b (b + 1) rfl)).1
  exact hF.eq_of_tgt _ _

lemma ringSingleCone_strictlyLE (F : ModuleCat.{u} A) (P : Complex A) (b : ℤ)
    (f : (single (ModuleCat.{u} A) (.up ℤ) b).obj F ⟶ P) [P.IsStrictlyLE b] :
    (CochainComplex.mappingCone f).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨isZero_single_obj_X (.up ℤ) b F (i + 1) (by omega),
    P.isZero_of_isStrictlyLE b i hi⟩

lemma ringSingleCone_strictlyGE (F : ModuleCat.{u} A) (P : Complex A) (a b : ℤ)
    (f : (single (ModuleCat.{u} A) (.up ℤ) b).obj F ⟶ P)
    [P.IsStrictlyGE a] (hab : a < b) : (CochainComplex.mappingCone f).IsStrictlyGE a :=
  CochainComplex.isStrictlyGE_mappingCone f b a a hab (le_refl _)

lemma ringSingleCoverCone_topTruncation (F : ModuleCat.{u} A)
    [Module.Finite A F] [Module.Projective A F]
    (P : Complex A) (hP : strictlyPerfectComplex A P) (b : ℤ)
    (f : (single (ModuleCat.{u} A) (.up ℤ) b).obj F ⟶ P)
    [P.IsStrictlyLE b] [Epi (homologyMap f b)] :
    strictlyPerfectComplex A ((CochainComplex.mappingCone f).truncLE (b - 1)) ∧
      QuasiIso ((CochainComplex.mappingCone f).ιTruncLE (b - 1)) := by
  have hC := strictlyPerfectComplex_mappingCone A f (strictlyPerfectComplex_single A F b) hP
  have htop := ringComplex_coverCone_topExact A f b
    (isZero_single_obj_homology (.up ℤ) b F (b + 1) (by omega))
  have : (CochainComplex.mappingCone f).IsStrictlyLE ((b - 1) + 1) := by
    simpa only [sub_add_cancel] using ringSingleCone_strictlyLE A F P b f
  exact ringComplex_topTruncation A _ hC (b - 1) (by simpa only [sub_add_cancel] using htop)

lemma ringSingleCoverCone_shorterModel (F : ModuleCat.{u} A)
    [Module.Finite A F] [Module.Projective A F]
    (P : Complex A) (hP : strictlyPerfectComplex A P) (a b : ℤ)
    (f : (single (ModuleCat.{u} A) (.up ℤ) b).obj F ⟶ P)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b] [Epi (homologyMap f b)] (hab : a < b) :
    ∃ Q : Complex A, strictlyPerfectComplex A Q ∧ Q.IsStrictlyGE a ∧ Q.IsStrictlyLE (b - 1) ∧
      ∃ i : Q ⟶ CochainComplex.mappingCone f, QuasiIso i := by
  obtain ⟨hQ, hi⟩ := ringSingleCoverCone_topTruncation A F P hP b f
  have : (CochainComplex.mappingCone f).IsStrictlyGE a :=
    ringSingleCone_strictlyGE A F P a b f hab
  have hge := ringComplex_truncLE_strictlyGE A (CochainComplex.mappingCone f) a (b - 1)
    (by omega)
  exact ⟨_, hQ, hge, inferInstance, _, hi⟩

end SerrePositivity.DifferentialGraded
end

end RingHomologyCoverCone

/-! ## RingDerivedFiniteCover（旧 SerrePositivity/DifferentialGraded/Perfect/RingDerivedFiniteCover.lean） -/

/-! # 導来対象の有限自由上端被覆と有限射影始域からの射の持ち上げ

既存の任意のHasDerivedCategoryを使う。導来圏のモデルや射クラスは変更しない。
-/

@[expose] public section RingDerivedFiniteCover
universe u w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma ringComplexDerived_map_surjective (P : Complex A) (hP : strictlyPerfectComplex A P)
    (K : Complex A) : Function.Surjective (DerivedCategory.Q.map (X := P) (Y := K)) := by
  let := strictlyPerfectComplex_isKProjective A P hP
  let q := _root_.HomotopyCategory.quotient (ModuleCat.{u} A) (.up ℤ)
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{u} A)
  intro f
  obtain ⟨u, hu⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P (q.obj K)).2
    (e.hom.app P ≫ f ≫ e.inv.app K)
  obtain ⟨g, hg⟩ := q.map_surjective u
  refine ⟨g, (cancel_epi (e.hom.app P)).1 ?_⟩
  have h := e.hom.naturality g
  change DerivedCategory.Qh.map (q.map g) ≫ e.hom.app K = e.hom.app P ≫
    DerivedCategory.Q.map g at h
  rw [hg, hu] at h
  simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using h.symm

lemma ringDerived_homologyMap_epi_of_chainMap {P K : Complex A} (f : P ⟶ K) (n : ℤ)
    [Epi (homologyMap f n)] :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map (DerivedCategory.Q.map f)) := by
  let e := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n
  have h : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
      (DerivedCategory.Q.map f) = e.hom.app P ≫ homologyMap f n ≫ e.inv.app K := by
    apply (cancel_mono (e.hom.app K)).1
    have hn : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
        (DerivedCategory.Q.map f) ≫ e.hom.app K = e.hom.app P ≫ homologyMap f n :=
      e.hom.naturality f
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id_app, ← Category.assoc]
    exact hn.trans (Category.comp_id _).symm
  rw [h]
  infer_instance

lemma ringDerived_exists_finiteFree_homologyCover (X : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    [Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj X)] :
    ∃ (m : ℕ) (f : DerivedCategory.Q.obj ((single (ModuleCat.{u} A) (.up ℤ) n).obj
        (ModuleCat.of A (Fin m → A))) ⟶ X),
      Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map f) := by
  let K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  let eh : H.obj X ≅ K.homology n := (H.mapIso e).symm ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app K
  let : Module.Finite A (K.homology n) := Module.Finite.equiv eh.toLinearEquiv
  obtain ⟨m, f, hf⟩ := ringComplex_exists_finiteFree_homologyCover A K n
  let := hf
  let := ringDerived_homologyMap_epi_of_chainMap A f n
  refine ⟨m, DerivedCategory.Q.map f ≫ e.hom, ?_⟩
  rw [H.map_comp]
  infer_instance

lemma ringDerivedRetract_topHomology_finite_usual (P : Complex A) (n : ℤ)
    [Module.Finite A (P.X n)] (hd : P.d n (n + 1) = 0)
    {X : DerivedCategory (ModuleCat.{u} A)} (a : Retract X (DerivedCategory.Q.obj P)) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj X) := by
  let : Module.Finite A
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} A) (.up ℤ) n).obj P) :=
    ringComplex_topHomology_finite A P n hd
  exact finiteModule_of_retract A
    ((a.map (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n)).trans
      (Retract.ofIso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app P)))

end SerrePositivity.DifferentialGraded
end

end RingDerivedFiniteCover

/-! ## RingRetractTriangle（旧 SerrePositivity/DifferentialGraded/Perfect/RingRetractTriangle.lean） -/

/-! # retractと補対象の三角形を有限射影複体上のconeで表す -/

@[expose] public section RingRetractTriangle
universe u w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex Pretriangulated
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma ringDerivedRetract_complement {X Y : DerivedCategory (ModuleCat.{u} A)} (a : Retract X Y) :
    ∃ (Z : DerivedCategory (ModuleCat.{u} A)) (e : Y ≅ X ⊞ Z), a.i ≫ e.hom = biprod.inl := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle a.i
  let T := Triangle.mk a.i g h
  obtain ⟨e, he, _⟩ := exists_iso_binaryBiproduct_of_distTriang T hT
    (T.mor₃_eq_zero_of_mono₁ hT (show Mono a.i from inferInstance))
  exact ⟨Z, e, he⟩

lemma ringDerived_chainMap_homology_epi {P K : Complex A} (f : P ⟶ K) (n : ℤ)
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map (DerivedCategory.Q.map f))] :
    Epi (homologyMap f n) := by
  let e := DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n
  have hn : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
      (DerivedCategory.Q.map f) ≫ e.hom.app K = e.hom.app P ≫ homologyMap f n :=
    e.hom.naturality f
  have : Epi (e.hom.app P ≫ homologyMap f n) := by
    rw [← hn]
    infer_instance
  exact epi_of_epi (e.hom.app P) _

lemma ringDerived_homology_biprodMap_epi (n : ℤ)
    {X Y Z W : DerivedCategory (ModuleCat.{u} A)} (f : X ⟶ Y) (g : Z ⟶ W)
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map f)]
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map g)] :
    Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map (biprod.map f g)) := by
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  let : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBiproducts H
  have he : H.map (biprod.map f g) = (H.mapBiprod X Z).hom ≫
      biprod.map (H.map f) (H.map g) ≫ (H.mapBiprod Y W).inv := by
    apply (cancel_mono (H.mapBiprod Y W).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biprod.hom_ext
    all_goals simp only [Functor.mapBiprod_hom, Category.assoc, biprod.lift_fst,
      biprod.lift_snd, biprod.lift_fst_assoc, biprod.lift_snd_assoc,
      biprod.map_fst, biprod.map_snd, ← H.map_comp]
  rw [he]
  infer_instance

lemma ringDerivedTriangle_sum_coneRetract
    (T U : Triangle (DerivedCategory (ModuleCat.{u} A)))
    (hT : T ∈ distTriang _) (hU : U ∈ distTriang _)
    (F : ModuleCat.{u} A) [Module.Finite A F] [Module.Projective A F]
    (P : Complex A) (b : ℤ)
    (e₁ : DerivedCategory.Q.obj ((single (ModuleCat.{u} A) (.up ℤ) b).obj F) ≅ T.obj₁ ⊞ U.obj₁)
    (e₂ : DerivedCategory.Q.obj P ≅ T.obj₂ ⊞ U.obj₂)
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) b).map T.mor₁)]
    [Epi ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) b).map U.mor₁)] :
    ∃ f : (single (ModuleCat.{u} A) (.up ℤ) b).obj F ⟶ P,
      Epi (homologyMap f b) ∧ Nonempty (Retract T.obj₃ (DerivedCategory.Q.obj
        (CochainComplex.mappingCone f))) := by
  let S := (single (ModuleCat.{u} A) (.up ℤ) b).obj F
  let h := e₁.hom ≫ biprod.map T.mor₁ U.mor₁ ≫ e₂.inv
  obtain ⟨f, hf⟩ := ringComplexDerived_map_surjective A S
    (strictlyPerfectComplex_single A F b) P h
  let V := triangleBiproduct T U
  let C := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  let e : C ≅ V := isoTriangleOfIso₁₂ C V (DerivedCategory.mappingCone_triangle_distinguished f)
    (triangleBiproduct_distinguished T U hT hU) e₁ e₂ (by
      change DerivedCategory.Q.map f ≫ e₂.hom = e₁.hom ≫ biprod.map T.mor₁ U.mor₁
      rw [hf]
      simp only [h, Category.assoc, Iso.inv_hom_id, Category.comp_id])
  let r : Retract T.obj₃ V.obj₃ :=
    { i := biprod.inl, r := biprod.fst, retract := biprod.inl_fst }
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) b
  have : Epi (H.map (DerivedCategory.Q.map f)) := by
    let := ringDerived_homology_biprodMap_epi A b T.mor₁ U.mor₁
    rw [hf]
    simp only [h, H.map_comp]
    infer_instance
  exact ⟨f, ringDerived_chainMap_homology_epi A f b,
    ⟨r.trans (Retract.ofIso (Triangle.π₃.mapIso e).symm)⟩⟩

end SerrePositivity.DifferentialGraded
end

end RingRetractTriangle

/-! ## RingRetractRangeReduction（旧 SerrePositivity/DifferentialGraded/Perfect/RingRetractRangeReduction.lean） -/

/-! # 有限射影複体の導来retractを一段短い次数幅へ帰着する -/

@[expose] public section RingRetractRangeReduction
universe u w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex Pretriangulated
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma ringDerivedRetract_reduce_range (P : Complex A) (hP : strictlyPerfectComplex A P)
    (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    {X : DerivedCategory (ModuleCat.{u} A)} (r : Retract X (DerivedCategory.Q.obj P))
    (hab : a < b) :
    ∃ F : ModuleCat.{u} A, Module.Finite A F ∧ Module.Projective A F ∧
      ∃ T : Triangle (DerivedCategory (ModuleCat.{u} A)), T ∈ distTriang _ ∧
        T.obj₁ = DerivedCategory.Q.obj ((single (ModuleCat.{u} A) (.up ℤ) b).obj F) ∧
        T.obj₂ = X ∧ ∃ P' : Complex A, strictlyPerfectComplex A P' ∧
          P'.IsStrictlyGE a ∧ P'.IsStrictlyLE (b - 1) ∧
            Nonempty (Retract T.obj₃ (DerivedCategory.Q.obj P')) := by
  obtain ⟨Z, e, _⟩ := ringDerivedRetract_complement A r
  let rZ : Retract Z (DerivedCategory.Q.obj P) :=
    { i := biprod.inr ≫ e.inv
      r := e.hom ≫ biprod.snd
      retract := by simp only [Category.assoc, Iso.inv_hom_id_assoc, biprod.inr_snd] }
  let := (hP.2 b).1
  have hd : P.d b (b + 1) = 0 := (P.isZero_of_isStrictlyLE b (b + 1) (by omega)).eq_of_tgt _ _
  let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) b
  let : Module.Finite A (H.obj X) := ringDerivedRetract_topHomology_finite_usual A P b hd r
  let : Module.Finite A (H.obj Z) := ringDerivedRetract_topHomology_finite_usual A P b hd rZ
  obtain ⟨m, fx, hx⟩ := ringDerived_exists_finiteFree_homologyCover A X b
  obtain ⟨n, fz, hz⟩ := ringDerived_exists_finiteFree_homologyCover A Z b
  obtain ⟨Y, gx, dx, hT⟩ := distinguished_cocone_triangle fx
  obtain ⟨W, gz, dz, hU⟩ := distinguished_cocone_triangle fz
  let T := Triangle.mk fx gx dx
  let U := Triangle.mk fz gz dz
  let F₀ := ModuleCat.of A (Fin m → A)
  let F₁ := ModuleCat.of A (Fin n → A)
  let F := F₀ ⊞ F₁
  let ef := (ModuleCat.biprodIsoProd F₀ F₁).symm.toLinearEquiv
  let : Module.Finite A F := Module.Finite.equiv ef
  let : Module.Projective A F := Module.Projective.of_equiv' ef
  let S := single (ModuleCat.{u} A) (.up ℤ) b
  let : PreservesBinaryBiproducts S := preservesBinaryBiproducts_of_preservesBiproducts S
  let : PreservesBinaryBiproducts (DerivedCategory.Q (C := ModuleCat.{u} A)) :=
    preservesBinaryBiproducts_of_preservesBiproducts _
  let e₁ : DerivedCategory.Q.obj (S.obj F) ≅ T.obj₁ ⊞ U.obj₁ :=
    DerivedCategory.Q.mapIso (S.mapBiprod F₀ F₁) ≪≫
      DerivedCategory.Q.mapBiprod (S.obj F₀) (S.obj F₁)
  let : Epi (H.map T.mor₁) := hx
  let : Epi (H.map U.mor₁) := hz
  obtain ⟨f, hf, ⟨rY⟩⟩ := ringDerivedTriangle_sum_coneRetract A T U hT hU F P b e₁ e
  let := hf
  obtain ⟨P', hP', hge, hle, i, hi⟩ := ringSingleCoverCone_shorterModel A F P hP a b f hab
  let := hi
  let e' : DerivedCategory.Q.obj P' ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone f) :=
    asIso (DerivedCategory.Q.map i)
  exact ⟨F₀, inferInstance, inferInstance, T, hT, rfl, rfl,
    P', hP', hge, hle, ⟨rY.trans (Retract.ofIso e'.symm)⟩⟩

end SerrePositivity.DifferentialGraded
end

end RingRetractRangeReduction

/-! ## RingRetractSingle（旧 SerrePositivity/DifferentialGraded/Perfect/RingRetractSingle.lean） -/

/-! # 一次数の有限射影複体の導来retract

single関手の完全忠実性で冪等元を加群へ戻して分裂し、有限射影加群のsingleを得る。
-/

@[expose] public section RingRetractSingle
universe u w

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex
variable (A : Type u) [CommRing A] [HasDerivedCategory.{w} (ModuleCat.{u} A)]

lemma ringDerivedRetract_single_finiteProjective (F : ModuleCat.{u} A)
    [Module.Finite A F] [Module.Projective A F] (n : ℤ)
    {X : DerivedCategory (ModuleCat.{u} A)}
    (a : Retract X (DerivedCategory.Q.obj ((single (ModuleCat.{u} A) (.up ℤ) n).obj F))) :
    ∃ G : ModuleCat.{u} A, Module.Finite A G ∧ Module.Projective A G ∧
      Nonempty (DerivedCategory.Q.obj ((single (ModuleCat.{u} A) (.up ℤ) n).obj G) ≅ X) := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) n
  let p := S.preimage (a.r ≫ a.i)
  have hp : p ≫ p = p := by
    apply S.map_injective
    rw [S.map_comp]
    simp only [p, S.map_preimage, Category.assoc, a.retract_assoc]
  obtain ⟨G, i, r, hir, hri⟩ := IsIdempotentComplete.idempotents_split F p hp
  let b : Retract G F := ⟨i, r, hir⟩
  have h₁ : S.map i ≫ S.map r = 𝟙 _ := by rw [← S.map_comp, hir, S.map_id]
  have h₂ : S.map r ≫ S.map i = a.r ≫ a.i := by
    rw [← S.map_comp, hri]
    exact S.map_preimage _
  let e : S.obj G ≅ X :=
    { hom := S.map i ≫ a.r
      inv := a.i ≫ S.map r
      hom_inv_id := by
        calc
          _ = S.map i ≫ (a.r ≫ a.i) ≫ S.map r := by simp only [Category.assoc]
          _ = S.map i ≫ (S.map r ≫ S.map i) ≫ S.map r := by rw [h₂]
          _ = _ := by simp only [← Category.assoc, h₁, Category.id_comp]
      inv_hom_id := by
        calc
          _ = a.i ≫ (S.map r ≫ S.map i) ≫ a.r := by simp only [Category.assoc]
          _ = a.i ≫ (a.r ≫ a.i) ≫ a.r := by rw [h₂]
          _ = _ := by simp only [← Category.assoc, a.retract, Category.id_comp] }
  exact ⟨G, finiteModule_of_retract A b,
    Module.Projective.of_split i.hom r.hom (congrArg (fun f => f.hom) hir), ⟨e⟩⟩

lemma ringDerivedRetract_pure_finiteRange (P : Complex A) (hP : strictlyPerfectComplex A P)
    (n : ℤ) [P.IsStrictlyGE n] [P.IsStrictlyLE n]
    {X : DerivedCategory (ModuleCat.{u} A)} (a : Retract X (DerivedCategory.Q.obj P)) :
    ∃ K : Complex A, strictlyPerfectComplex A K ∧ K.IsStrictlyGE n ∧ K.IsStrictlyLE n ∧
      Nonempty (DerivedCategory.Q.obj K ≅ X) := by
  obtain ⟨F, ⟨e⟩⟩ := P.exists_iso_single n
  let ev : P.X n ≅ F := HomologicalComplex.Hom.isoApp e n ≪≫ singleObjXSelf (.up ℤ) n F
  let := (hP.2 n).1
  let := (hP.2 n).2
  let : Module.Finite A F := Module.Finite.equiv ev.toLinearEquiv
  let : Module.Projective A F := Module.Projective.of_equiv' ev.toLinearEquiv
  obtain ⟨G, hf, hp, ⟨eG⟩⟩ := ringDerivedRetract_single_finiteProjective A F n
    (a.trans (Retract.ofIso (DerivedCategory.Q.mapIso e)))
  let := hf
  let := hp
  exact ⟨_, strictlyPerfectComplex_single A G n, inferInstance, inferInstance, ⟨eG⟩⟩

end SerrePositivity.DifferentialGraded
end

end RingRetractSingle

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "7.2.4.25" (partial := stronger-hyp) "仮定：通常可換環上の有界な有限生成射影複体（Lean が強い：この通常の dg 導来模型で有限射影表示を指定する）。結論：その導来像が perfect となる（有限射影複体から perfect への方向に一致）。原典は項の有限生成性のみを印字しているが、Lean は有限射影性を仮定する。一般の加群スペクトルの表示との同値は含まれない。"] _root_.SerrePositivity.DifferentialGraded.strictlyPerfectComplex_ringDerived_perfect
attribute [cite HA "7.2.4.5" (partial := component) "仮定：通常可換環上の有界有限射影複体 P、P の厳密な余鎖上限 n とその導来 retract X（Lean が強い：この模型の上端の次数を指定する）。結論：上端の Hⁿ(X) が有限生成となる（最低ホモトピー次数の有限表示性から従う有限生成の部分に一致）。有限表示性そのものと一般の連結環スペクトルでの下限の存在は含まれない。"] _root_.SerrePositivity.DifferentialGraded.ringDerivedRetract_topHomology_finite_of_strictlyPerfect
