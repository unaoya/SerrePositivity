module

public import SerrePositivity.KST.DerivedBlowup.FiniteOverlapTwistDGModel
public import SerrePositivity.DifferentialGraded.Derived.RestrictionTriangles

/-!
概要：KST v4 §3.1（pp.11–14）の dg 模型上の捻りと指定導来捻りの H⁰ 比較。
方針：全図式 dg 加群への包含と捻りの可換式を、既存の導来制限比較へ接続する。
規約：原典とは異なる図式加群模型での比較。層の降下はこの比較からは結論しない。
使われ方：dg 模型上の捻りの実装が指定導来自己同値を表すことの確認。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory CategoryTheory.Functor DifferentialGraded

variable (R : Type u) [CommRing R] {I : Type} [DecidableEq I] (a : I → R)

/-- 概要：cartesian perfect 射影的 dg 模型から全図式 dg 加群への包含。
方針：二つの既存充満 dg 包含を合成する。
規約：KST §3.1。使われ方：指定主導来比較への接続。 -/
def blowupDiagramModuleInclusion :
    DGFunctor R (CartesianPerfectDiagramDGModel R a)
      (RightModule R (BlowupDiagramCoefficientObject R a)ᵒᵖ) :=
  (cartesianPerfectDiagramInclusion R a).comp
    (projectiveDiagramModuleInclusion (finiteOverlapDGAlgebraDiagram R a))

/-- 概要：dg 模型の捻りと全 dg 加群への包含は可換。
方針：対象は同じ制限加群、Hom は同じ全次数制限写像である。
規約：KST §3.1。使われ方：H⁰ と導来局所化へ移す可換式。 -/
theorem blowupTwistDGFunctor_inclusion (m : ℤ) :
    (blowupTwistDGFunctor R a m).comp (blowupDiagramModuleInclusion R a) =
      (blowupDiagramModuleInclusion R a).comp (finiteOverlapDGTwistAction R a m) := by
  refine EnrichedFunctor.ext (Complex R) (fun _ => rfl) ?_
  intro M N
  simp only [eqToHom_refl, Category.comp_id]
  change (finiteOverlapDGTwistAction R a m).map M.val.val N.val.val ≫ (𝟙 _ ≫ 𝟙 _) =
    (𝟙 _ ≫ 𝟙 _) ≫ (finiteOverlapDGTwistAction R a m).map M.val.val N.val.val
  simp only [Category.id_comp, Category.comp_id]

/-- 概要：既存の cartesian perfect H⁰ 比較を全導来圏へ含めた経路の同定。
方針：充満部分圏への持ち上げを忘れ、H⁰ の合成則を使う。
規約：KST §3.1。使われ方：指定部分圏比較を一般の導来制限比較と合成する。 -/
theorem cartesianPerfectDiagramToDerived_inclusion :
    cartesianPerfectDiagramToDerived R a ⋙ (diagramCartesianPerfect R a).ι =
      (blowupDiagramModuleInclusion R a).onHomotopy ⋙
        moduleHomotopyToDerivedClosed R (BlowupDiagramCoefficientObject R a)ᵒᵖ := by
  rw [blowupDiagramModuleInclusion, DGFunctor.onHomotopy_comp]
  rfl

/-- 概要：dg 模型の H⁰ 捻りと指定導来捻りを結ぶ自然同型。
方針：包含と捻りの厳密可換式を、主 H⁰–導来制限比較の自然同型へ合成する。
規約：KST §3.1、比較は元の Koszul 模型と指定導来作用を保つ。
使われ方：dg レベルの捻りが構成済み導来自己同値を表すことの確認。 -/
def blowupTwistDGDerivedComparison (m : ℤ) :
    (blowupTwistDGFunctor R a m).onHomotopy ⋙
        (cartesianPerfectDiagramToDerived R a ⋙ (diagramCartesianPerfect R a).ι) ≅
      (cartesianPerfectDiagramToDerived R a ⋙ (diagramCartesianPerfect R a).ι) ⋙
        finiteOverlapDerivedTwistAction R a m := by
  rw [cartesianPerfectDiagramToDerived_inclusion]
  let B := blowupDiagramModuleInclusion R a
  let T := blowupTwistDGFunctor R a m
  let G := finiteOverlapDGTwistAction R a m
  let Q := moduleHomotopyToDerivedClosed R (BlowupDiagramCoefficientObject R a)ᵒᵖ
  have h : T.onHomotopy ⋙ B.onHomotopy = B.onHomotopy ⋙ G.onHomotopy := by
    rw [← DGFunctor.onHomotopy_comp, ← DGFunctor.onHomotopy_comp]
    exact congrArg DGFunctor.onHomotopy (blowupTwistDGFunctor_inclusion R a m)
  exact (Functor.associator T.onHomotopy B.onHomotopy Q).symm ≪≫
    isoWhiskerRight (eqToIso h) Q ≪≫
    Functor.associator B.onHomotopy G.onHomotopy Q ≪≫
    isoWhiskerLeft B.onHomotopy (dgDerivedRestrictionHomotopyIso R
      (BlowupDiagramCoefficientObject R a)ᵒᵖ (BlowupDiagramCoefficientObject R a)ᵒᵖ
      (finiteOverlapTwistDGFunctor R a m).op) ≪≫
    (Functor.associator B.onHomotopy Q (finiteOverlapDerivedTwistAction R a m)).symm

/-- 概要：充満部分圏の包含後の自然同型を部分圏へ戻す。
方針：成分と自然性を元の圏で計算する。
規約：KST §3.1 の模型比較の一般補題。使われ方：大きな関手定義を展開せず持ち上げる。 -/
def liftFullSubcategoryNatIso {C D : Type*} [Category* C] [Category* D]
    (P : ObjectProperty D) {F G : C ⥤ P.FullSubcategory}
    (e : F ⋙ P.ι ≅ G ⋙ P.ι) : F ≅ G :=
  NatIso.ofComponents (fun X => P.isoMk (e.app X)) (by
    intro X Y f
    apply ObjectProperty.hom_ext
    exact e.hom.naturality f)

/-- 概要：dg 模型の H⁰ 捻りは既存 cartesian perfect 導来自己同値と自然に対応する。
方針：全導来圏での指定自然同型を完全忠実な包含に沿って引き戻す。
規約：KST §3.1。使われ方：実際の部分圏の中で捻りの比較を使う。 -/
def blowupTwistDGCartesianComparison (m : ℤ) :
    (blowupTwistDGFunctor R a m).onHomotopy ⋙ cartesianPerfectDiagramToDerived R a ≅
      cartesianPerfectDiagramToDerived R a ⋙ (blowupDerivedTwistEquivalence R a m).functor :=
  liftFullSubcategoryNatIso (diagramCartesianPerfect R a)
    (blowupTwistDGDerivedComparison R a m)

/-- 概要：dg 模型の整数捻りの H⁰ 関手は同値。
方針：既存の模型比較と導来捻りの同値を、指定自然同型で接続して消去する。
規約：KST §3.1。使われ方：捻りの可逆性を実際の dg 模型の H⁰ で保証する。 -/
instance blowupTwistDGFunctorHomotopyIsEquivalence (m : ℤ) :
    (blowupTwistDGFunctor R a m).onHomotopy.IsEquivalence := by
  have : ((blowupTwistDGFunctor R a m).onHomotopy ⋙
      cartesianPerfectDiagramToDerived R a).IsEquivalence :=
    Functor.isEquivalence_of_iso (blowupTwistDGCartesianComparison R a m).symm
  exact Functor.isEquivalence_of_comp_right _ (cartesianPerfectDiagramToDerived R a)

end SerrePositivity.KST.DerivedBlowup
