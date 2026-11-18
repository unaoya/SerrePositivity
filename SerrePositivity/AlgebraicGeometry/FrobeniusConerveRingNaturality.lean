module

public import SerrePositivity.AlgebraicGeometry.FrobeniusConerveRingDiagram
public import SerrePositivity.AlgebraicGeometry.RingDirectLimitNaturality

/-!
概要：同じ conerve の環の反復図式の標準比較を、その全ての次数の射に自然にする。
方針：元の conerve の環準同型を有向系の自然変換へ渡し、恒等成分で照合する。
規約：元の環・面・退化写像を保持する。
使われ方：同じ係数環の余極限の比較を自然な余単体図式へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable (f : Arrow CommRingCat.{u}) (p : ℕ) (hp : p.Prime)
variable (hA : (p : f.left) = 0) (hB : (p : f.right) = 0)

/-- 同じ conerve の実際の環準同型を、各段の Frobenius 系の射にする。 -/
def frobeniusConerveRingSystemMap {n m : SimplexCategory} (a : n ⟶ m) :
    ringDirectSystemFunctor (frobeniusDirectSystemMap (f.cechConerve.obj n) p hp
      (frobeniusConerve_primeCast f p hA n)) ⟶
      ringDirectSystemFunctor (frobeniusDirectSystemMap (f.cechConerve.obj m) p hp
        (frobeniusConerve_primeCast f p hA m)) :=
  ringDirectSystemNatTrans _ _ (fun _ ↦ (f.cechConerve.map a).hom)
    (fun i j h x ↦ frobeniusDirectSystemMap_naturality p hp
      (frobeniusConerve_primeCast f p hA n) (frobeniusConerve_primeCast f p hA m)
      (f.cechConerve.map a).hom i j h x)

set_option backward.isDefEq.respectTransparency false in
/-- 恒等成分の標準比較は、元の conerve の全ての次数の射に自然。 -/
theorem frobeniusConerveRingDiagramIso_naturality {n m : SimplexCategory} (a : n ⟶ m) :
    frobeniusConerveRingSystemMap f p hp hA a ≫
        (frobeniusConerveRingDiagramIso f p hp hA hB m).hom =
      (frobeniusConerveRingDiagramIso f p hp hA hB n).hom ≫
        Functor.whiskerLeft
          (frobeniusArrowDiagram f p hp hA hB ⋙ CosimplicialObject.cechConerve)
          ((evaluation SimplexCategory CommRingCat.{u}).map a) := by
  apply NatTrans.ext
  funext i
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  rfl

end SerrePositivity.AlgebraicGeometry
