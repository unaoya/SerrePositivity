module

public import SerrePositivity.KST.LocalizingInvariants.HomotopySquareFiberMap

/-!
概要：任意の二つの BF 射の間の指定可換ホモトピーから、整数 fiber 群の比較を構成する。
方針：標的の右辺を fibration 置換し、単位が誘導する同じ fiber 比較の群同型で戻す。
規約：源・標的の右辺に fibration 性を仮定しない。使われ方：一般の prism の接続射。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.Spectra SerrePositivity.KST.Spectra.OmegaSpectrum
namespace SerrePositivity.KST.LocalizingInvariants.HomotopySquareGroups

variable {X Y X' Y' : OmegaSpectrum.{u}} (p : X ⟶ Y) (q : X' ⟶ Y')

lemma unitSquare : q ≫ 𝟙 Y' = fibrationReplacementUnit q ≫
    fibrationReplacementProjection q := by rw [Category.comp_id, fibrationReplacement_fac]

def unitFiberMap : homotopyFiber q ⟶ homotopyFiber (fibrationReplacementProjection q) :=
  HomotopyFiberComparison.map q (fibrationReplacementProjection q)
    (fibrationReplacementUnit q) (𝟙 Y') (unitSquare q)

lemma unitFiberMap_piIsomorphism : PiIsomorphism (unitFiberMap q) := by
  apply HomotopyFiberComparison.map_piIsomorphism
    q (fibrationReplacementProjection q) _ _ _ (fibrationReplacementUnit_piIsomorphism q)
  intro j
  rw [homotopyMap_id]
  exact Function.bijective_id

def unitFiberEquiv (j : ℤ) : homotopyGroup (homotopyFiber q) j ≃*
    homotopyGroup (homotopyFiber (fibrationReplacementProjection q)) j :=
  MulEquiv.ofBijective (homotopyMap (unitFiberMap q) j) (unitFiberMap_piIsomorphism q j)

lemma unitFiberEquiv_boundary (j : ℤ) (x : homotopyGroup Y' (j + 1)) :
    unitFiberEquiv q j (homotopyFiberBoundary q j x) =
      homotopyFiberBoundary (fibrationReplacementProjection q) j x := by
  change homotopyMap (unitFiberMap q) j (homotopyFiberBoundary q j x) = _
  have h := HomotopyFiberComparison.boundary_natural q (fibrationReplacementProjection q)
    (fibrationReplacementUnit q) (𝟙 Y') (unitSquare q) j x
  change homotopyMap (unitFiberMap q) j (homotopyFiberBoundary q j x) =
    homotopyFiberBoundary (fibrationReplacementProjection q) j
      (homotopyMap (𝟙 Y') (j + 1) x) at h
  rw [homotopyMap_id, MonoidHom.id_apply] at h
  exact h

variable (a : X ⟶ X') (b : Y ⟶ Y')
  (γ : (mappingSpace X Y').Edge (vertexOfHom (a ≫ q)) (vertexOfHom (p ≫ b)))

def replacedEdge : (mappingSpace X Y').Edge
    (vertexOfHom ((a ≫ fibrationReplacementUnit q) ≫ fibrationReplacementProjection q))
    (vertexOfHom (p ≫ b)) :=
  γ.ofEq (congrArg vertexOfHom (by rw [Category.assoc, fibrationReplacement_fac])) rfl

def replacedFiberMap : homotopyFiber p ⟶ homotopyFiber (fibrationReplacementProjection q) :=
  HomotopySquareFiber.map p (fibrationReplacementProjection q)
    (a ≫ fibrationReplacementUnit q) b (replacedEdge p q a b γ)
    (fibrationReplacementProjection_fibration q)

def groupMap (j : ℤ) : homotopyGroup (homotopyFiber p) j →*
    homotopyGroup (homotopyFiber q) j :=
  (unitFiberEquiv q j).symm.toMonoidHom.comp (homotopyMap (replacedFiberMap p q a b γ) j)

lemma boundary_natural (j : ℤ) (x : homotopyGroup Y (j + 1)) :
    groupMap p q a b γ j (homotopyFiberBoundary p j x) =
      homotopyFiberBoundary q j (homotopyMap b (j + 1) x) := by
  apply (unitFiberEquiv q j).injective
  change (unitFiberEquiv q j) ((unitFiberEquiv q j).symm
      (homotopyMap (replacedFiberMap p q a b γ) j (homotopyFiberBoundary p j x))) = _
  rw [MulEquiv.apply_symm_apply, unitFiberEquiv_boundary]
  exact HomotopySquareFiber.boundary_natural _ _ _ _ _ _ j x

lemma boundaryHom_natural (j : ℤ) :
    (groupMap p q a b γ j).comp (homotopyFiberBoundary p j) =
      (homotopyFiberBoundary q j).comp (homotopyMap b (j + 1)) := by
  ext x
  exact boundary_natural p q a b γ j x

end SerrePositivity.KST.LocalizingInvariants.HomotopySquareGroups
