module

public import SerrePositivity.AlgebraicGeometry.OpenAtlasDiagonalEquations
public import SerrePositivity.AlgebraicGeometry.OpenAtlasTripleEquations

/-!
概要：段の gluing に要る六種の式の具体的な入力を一つの有限族へ組み立てる。
方針：対角・反転・三重交叉の六種の検証済みの入力を有限和の各成分に入れる。
規約：有限族の各入力は源・標的・比較・式の証人を実際に保持する。
使われ方：G2 の有限個の式の同じ係数段への移送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
open _root_.AlgebraicGeometry CategoryTheory Limits
universe u v
variable {k : Type v} [CommRing k] [IsNoetherianRing k]
  {R : Type u} [CommRing R] [Algebra k R]
  {I : Type u} {X : Scheme.{u}} {U : I → Scheme.{u}} {j : ∀ i, U i ⟶ X}
  [∀ i, IsOpenImmersion (j i)] {f : X ⟶ Spec (CommRingCat.of R)}
  (m : OpenAtlasModelData k U j f)
  {B : Scheme.{u}} (b : Spec (CommRingCat.of R) ⟶ B)
  (γ : B ⟶ Spec (CommRingCat.of m.A))
  (h : b ≫ γ = Spec.map (CommRingCat.ofHom (algebraMap m.A R)))

variable (l : ∀ e, pullback γ (m.atlasArrowFamily e).sourceMap ⟶
    pullback γ (m.atlasArrowFamily e).targetMap)
  (hl : ∀ e, l e ≫ pullback.fst γ (m.atlasArrowFamily e).targetMap =
    pullback.fst γ (m.atlasArrowFamily e).sourceMap)
  (hn : ∀ e, (m.atlasArrowFamily e).comparisonAt b γ h ≫ l e ≫
    pullback.snd γ (m.atlasArrowFamily e).targetMap = (m.atlasArrowFamily e).arrow)
/-- 六種の式を一つの有限族の具体的な一致判定の入力にする。 -/
def atlasEquationFamily (e : (Fin 3 × I) ⊕ ((I × I) ⊕ (Fin 2 × I × I × I))) :
    CartesianModelEquation b := by
  rcases e with ⟨r, i⟩ | (⟨i, a⟩ | ⟨r, i, a, c⟩)
  · exact Fin.cases (m.diagonalRightEquation b γ h l hl hn i)
      (fun s ↦ Fin.cases (m.diagonalLeftEquation b γ h l hl hn i)
        (fun _ ↦ m.reverseDiagonalEquation b γ h l hl hn i) s) r
  · exact m.reverseInverseEquation b γ h l hl hn i a
  · exact Fin.cases (m.tripleFstEquation b γ h l hl hn i a c)
      (fun _ ↦ m.tripleSndEquation b γ h l hl hn i a c) r

end SerrePositivity.AlgebraicGeometry.OpenAtlasModelData
