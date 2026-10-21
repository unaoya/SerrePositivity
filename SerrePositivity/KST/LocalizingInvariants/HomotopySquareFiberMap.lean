module

public import SerrePositivity.KST.LocalizingInvariants.FiberMappingPathLift
public import SerrePositivity.KST.LocalizingInvariants.HomotopyFiberMapComparison

/-!
概要：指定した全 BF 写像空間の辺で可換する正方形から、元の fiber の実比較射を得る。
方針：標的の fibration に指定辺を持ち上げ、厳密比較の接続射の自然性を適用する。
規約：指定辺をデータに保持する。使われ方：fiber 図式の prism への自然性の移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.HomotopySquareFiber

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')
  (a : X ⟶ X') (b : Y ⟶ Y')
  (γ : (mappingSpace X Y').Edge (vertexOfHom (a ≫ q)) (vertexOfHom (p ≫ b)))
  (hq : ∀ n, Fibration (q.app n).right)

def squareLift : FiberMapping.PathLift q a (p ≫ b) γ :=
  FiberMapping.pathLift q a (p ≫ b) γ hq

def map : homotopyFiber p ⟶ homotopyFiber q :=
  HomotopyFiberComparison.map p q (squareLift p q a b γ hq).map b
    (squareLift p q a b γ hq).fac.symm

lemma boundary_natural (j : ℤ) (x : homotopyGroup Y (j + 1)) :
    homotopyMap (map p q a b γ hq) j (homotopyFiberBoundary p j x) =
      homotopyFiberBoundary q j (homotopyMap b (j + 1) x) :=
  HomotopyFiberComparison.boundary_natural _ _ _ _ _ j x

lemma boundaryHom_natural (j : ℤ) :
    (homotopyMap (map p q a b γ hq) j).comp (homotopyFiberBoundary p j) =
      (homotopyFiberBoundary q j).comp (homotopyMap b (j + 1)) := by
  ext x
  exact boundary_natural p q a b γ hq j x

lemma inclusion_hom :
    SpectrumHo.hom (map p q a b γ hq) ≫ SpectrumHo.hom (homotopyFiberInclusion q) =
      SpectrumHo.hom (homotopyFiberInclusion p) ≫ SpectrumHo.hom a := by
  rw [← SpectrumHo.hom_comp]
  change SpectrumHo.hom (HomotopyFiberComparison.map _ _ _ _ _ ≫ _) = _
  rw [HomotopyFiberComparison.map_inclusion, SpectrumHo.hom_comp,
    ← (squareLift p q a b γ hq).hom]

lemma map_piIsomorphism (ha : PiIsomorphism a) (hb : PiIsomorphism b) :
    PiIsomorphism (map p q a b γ hq) := by
  apply HomotopyFiberComparison.map_piIsomorphism p q _ b _ _ hb
  intro j
  rw [← FiberMapping.PathLift.homotopyMap q a (p ≫ b) γ
    (squareLift p q a b γ hq) j]
  exact ha j

end SerrePositivity.KST.LocalizingInvariants.HomotopySquareFiber
