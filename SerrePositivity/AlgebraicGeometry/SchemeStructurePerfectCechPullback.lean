module

public import SerrePositivity.AlgebraicGeometry.SchemeStructurePerfectCechComparison
public import SerrePositivity.AlgebraicGeometry.SchemeCechPreimage

/-!
概要：実際の構造層の環の Frobenius 順極限に、スキームの射の引き戻しを入れる。
方針：構造層の環準同型に同じ Frobenius 順極限を適用し、2e の逆像被覆の比較を使う。
規約：平坦性は仮定しない。閉厚化と底変換にも同じ射を用いる。
使われ方：F8 の共通細分と底変換・閉厚化の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory TopologicalSpace _root_.AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- スキームの射による実際の切断環の引き戻しの自然変換。 -/
def schemeStructureRingPullbackCoefficient :
    Y.presheaf ⟶ (Opens.map f.base).op ⋙ X.presheaf where
  app U := f.app U.unop
  naturality {U V} i := f.naturality i

variable (p : ℕ) (hp : p.Prime)
variable (hY : ∀ O, (p : Y.presheaf.obj O) = 0)
variable (hX : ∀ O, (p : X.presheaf.obj O) = 0)

/-- 実際の切断環の引き戻しに同じ Frobenius 順極限を適用する。 -/
def schemeStructurePerfectPullbackCoefficient :
    frobeniusRingDiagram Y.presheaf p hp hY ⟶
      (Opens.map f.base).op ⋙ frobeniusRingDiagram X.presheaf p hp hX :=
  frobeniusRingDiagramMap p hp hY
    (hE := fun O ↦ hX ((Opens.map f.base).op.obj O))
    (schemeStructureRingPullbackCoefficient f)

variable {ι κ : Type} [DecidableEq ι] [DecidableEq κ]

/-- 実際の構造層の Frobenius 順極限の Čech 複体の引き戻し。 -/
def schemeStructurePerfectCechPullbackMap (U : ι → Y.Opens) :=
  schemeCechPullbackMap f (frobeniusRingDiagram X.presheaf p hp hX)
    (schemeStructurePerfectPullbackCoefficient f p hp hY hX) U

/-- 引き戻しは Frobenius 順極限後も同じ細分写像と可換。 -/
theorem schemeStructurePerfectCechPullbackMap_refinement
    (U : ι → Y.Opens) (V : κ → Y.Opens) (ρ : κ → ι)
    (hρ : ∀ j, V j ≤ U (ρ j)) :
    openCoverCechRefinementMap (frobeniusRingDiagram Y.presheaf p hp hY) U V ρ hρ ≫
        schemeStructurePerfectCechPullbackMap f p hp hY hX V =
      schemeStructurePerfectCechPullbackMap f p hp hY hX U ≫
        openCoverCechRefinementMap (frobeniusRingDiagram X.presheaf p hp hX)
          (fun i ↦ f ⁻¹ᵁ U i) (fun j ↦ f ⁻¹ᵁ V j) ρ
          (fun j ↦ ((Opens.map f.base).map (homOfLE (hρ j))).le) :=
  schemeCechPullbackMap_refinement f _
    (schemeStructurePerfectPullbackCoefficient f p hp hY hX) U V ρ hρ

end SerrePositivity.AlgebraicGeometry
