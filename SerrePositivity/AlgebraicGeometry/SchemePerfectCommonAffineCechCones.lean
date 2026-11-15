module

public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechComparison
public import SerrePositivity.AlgebraicGeometry.CechConeQuasiIsoAcyclic

/-!
概要：実際の有限アフィン細分の余鎖写像の cone の完全性を供給する。
方針：既存の同じ細分写像の準同型性を、明示的な cone の完全性へ渡す。
規約：細分の完全性を追加仮定にせず、被覆性とアフィン性から得る。
使われ方：共通細分での射影四角形の全複体の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits TopologicalSpace _root_.AlgebraicGeometry
universe u
variable (Y : Scheme.{u}) [IsAffineHom (pullback.diagonal (terminal.from Y))]
variable (p : ℕ) (hp : p.Prime) (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
variable {ι κ : Type} [LinearOrder ι] [Fintype ι] [LinearOrder κ] [Fintype κ]

/-- 有限アフィン細分の実際の Frobenius 係数の余鎖写像の cone は完全。
Stacks 30.2.6 の被覆比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem schemeStructurePerfectCechRefinement_cone_acyclic
    (U : ι → Y.Opens) (V : κ → Y.Opens) (ρ : κ → ι)
    (hρ : ∀ j, V j ≤ U (ρ j))
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hcV : (⨆ j, V j) = ⊤) :
    (cechRefinementCone
      (fullCechComplex (openCoverCechDiagram (frobeniusRingDiagram Y.presheaf p hp hY) U))
      (fullCechComplex (openCoverCechDiagram (frobeniusRingDiagram Y.presheaf p hp hY) V))
      (openCoverCechRefinementMap (frobeniusRingDiagram Y.presheaf p hp hY) U V ρ hρ)).Acyclic :=
  cechRefinementCone_acyclic_of_quasiIso _ _ _
    (fun q ↦ schemeStructureFrobeniusCechRefinement_quasiIsoAt
      Y p hp hY U V ρ hρ hU hV hcV q)

/-- 二つの有限アフィン被覆から、既存の同じ共通細分への両写像の cone は完全。
Stacks 30.2.6 の被覆比較に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する
（Stacks 30.2.6）が、この比較は形式化しない。 -/
theorem schemeStructurePerfectCommonAffineCech_cones
    (U : ι → Y.Opens) (V : κ → Y.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j))
    (hcU : (⨆ i, U i) = ⊤) (hcV : (⨆ j, V j) = ⊤) :
    let P := frobeniusRingDiagram Y.presheaf p hp hY
    let W := schemeFiniteCommonOpenCover U V
    (cechRefinementCone (fullCechComplex (openCoverCechDiagram P U))
      (fullCechComplex (openCoverCechDiagram P W))
      (openCoverCechRefinementMap P U W
        (schemeFiniteCommonCoverLeft (ι := ι) (κ := κ))
        (schemeFiniteCommonOpenCover_le_left U V))).Acyclic ∧
    (cechRefinementCone (fullCechComplex (openCoverCechDiagram P V))
      (fullCechComplex (openCoverCechDiagram P W))
      (openCoverCechRefinementMap P V W
        (schemeFiniteCommonCoverRight (ι := ι) (κ := κ))
        (schemeFiniteCommonOpenCover_le_right U V))).Acyclic := by
  constructor
  · exact schemeStructurePerfectCechRefinement_cone_acyclic Y p hp hY U _ _
      (schemeFiniteCommonOpenCover_le_left U V) hU
      (schemeFiniteCommonOpenCover_isAffineOpen U V hU hV)
      (schemeFiniteCommonOpenCover_iSup U V hcU hcV)
  · exact schemeStructurePerfectCechRefinement_cone_acyclic Y p hp hY V _ _
      (schemeFiniteCommonOpenCover_le_right U V) hV
      (schemeFiniteCommonOpenCover_isAffineOpen U V hU hV)
      (schemeFiniteCommonOpenCover_iSup U V hcU hcV)

end SerrePositivity.AlgebraicGeometry
