module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareReindex

/-!
概要：同じ全経路の表示変更から、同じ両端を持つ別経路の端点と底も移す。
方針：参照経路の全射の等式から、両評価と底射影の等式を取り出す。
規約：移す経路の全射は変えない。使われ方：native class 合成への二重経路の表示移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q q' : W ⟶ B} {a b a' b' : W ⟶ algebra B N}
  (v : RelativeWitness q N a b) (v' : RelativeWitness q' N a' b')
  (h : v.hom = v'.hom)

/-- 別の参照表示と同じ両端へ、元の経路の全射を保持して移す。 -/
def transferEndpoints (w : RelativeWitness q N a b) : RelativeWitness q' N a' b' where
  hom := w.hom
  source_eq := w.source_eq.trans (RelativeWitnessSquare.reindex_source v' h)
  target_eq := w.target_eq.trans (RelativeWitnessSquare.reindex_target v' h)
  projection_eq := w.projection_eq.trans (congrArg
    (fun k => k ≫ DGAlgebra.Path.diagonal R B) (RelativeWitnessSquare.reindex_base v' h))

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
