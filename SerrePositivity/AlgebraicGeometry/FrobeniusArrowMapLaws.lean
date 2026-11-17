module

public import SerrePositivity.AlgebraicGeometry.FrobeniusArrowNaturality

/-!
概要：同じ矢印の Frobenius 図式と順極限の写像の単位・合成を保つ。
方針：有限段の図式は成分で、実際の順極限は同じ有限段の元で照合する。
規約：元の矢印・写像・標数条件を保持する。
使われ方：行の交叉族の図式と、その後の模型の係数の図式。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable (p : ℕ) (hp : p.Prime) {f g h : Arrow CommRingCat.{u}}

/-- 同じ矢印の有限段の図式の写像は、元の恒等射を保つ。 -/
theorem frobeniusArrowDiagramMap_id (hA : (p : f.left) = 0) (hB : (p : f.right) = 0) :
    frobeniusArrowDiagramMap (𝟙 f) p hp hA hB hA hB = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  rfl

/-- 同じ矢印の有限段の図式の写像は、元の合成を保つ。 -/
theorem frobeniusArrowDiagramMap_comp (F : f ⟶ g) (G : g ⟶ h)
    (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)
    (hC : (p : g.left) = 0) (hD : (p : g.right) = 0)
    (hE : (p : h.left) = 0) (hF : (p : h.right) = 0) :
    frobeniusArrowDiagramMap (F ≫ G) p hp hA hB hE hF =
      frobeniusArrowDiagramMap F p hp hA hB hC hD ≫
        frobeniusArrowDiagramMap G p hp hC hD hE hF := by
  apply NatTrans.ext
  funext n
  rfl

/-- 同じ小さい添字の図式の写像は、元の恒等射を保つ。 -/
theorem frobeniusArrowSmallDiagramMap_id (hA : (p : f.left) = 0) (hB : (p : f.right) = 0) :
    frobeniusArrowSmallDiagramMap (𝟙 f) p hp hA hB hA hB = 𝟙 _ := by
  apply NatTrans.ext
  funext n
  rfl

/-- 同じ小さい添字の図式の写像は、元の合成を保つ。 -/
theorem frobeniusArrowSmallDiagramMap_comp (F : f ⟶ g) (G : g ⟶ h)
    (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)
    (hC : (p : g.left) = 0) (hD : (p : g.right) = 0)
    (hE : (p : h.left) = 0) (hF : (p : h.right) = 0) :
    frobeniusArrowSmallDiagramMap (F ≫ G) p hp hA hB hE hF =
      frobeniusArrowSmallDiagramMap F p hp hA hB hC hD ≫
        frobeniusArrowSmallDiagramMap G p hp hC hD hE hF := by
  apply NatTrans.ext
  funext n
  rfl

/-- 同じ実際の Frobenius 順極限の矢印の写像は、元の恒等射を保つ。 -/
theorem frobeniusDirectLimitArrowMap_id (hA : (p : f.left) = 0) (hB : (p : f.right) = 0) :
    frobeniusDirectLimitArrowMap (𝟙 f) p hp hA hB hA hB = 𝟙 _ := by
  apply Arrow.hom_ext
  · apply CommRingCat.hom_ext
    apply DirectLimit.Ring.hom_ext
    intro n
    ext x
    rfl
  · apply CommRingCat.hom_ext
    apply DirectLimit.Ring.hom_ext
    intro n
    ext x
    rfl

/-- 同じ実際の Frobenius 順極限の矢印の写像は、元の合成を保つ。 -/
theorem frobeniusDirectLimitArrowMap_comp (F : f ⟶ g) (G : g ⟶ h)
    (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)
    (hC : (p : g.left) = 0) (hD : (p : g.right) = 0)
    (hE : (p : h.left) = 0) (hF : (p : h.right) = 0) :
    frobeniusDirectLimitArrowMap (F ≫ G) p hp hA hB hE hF =
      frobeniusDirectLimitArrowMap F p hp hA hB hC hD ≫
        frobeniusDirectLimitArrowMap G p hp hC hD hE hF := by
  apply Arrow.hom_ext
  · apply CommRingCat.hom_ext
    apply DirectLimit.Ring.hom_ext
    intro n
    ext x
    rfl
  · apply CommRingCat.hom_ext
    apply DirectLimit.Ring.hom_ext
    intro n
    ext x
    rfl

end SerrePositivity.AlgebraicGeometry
