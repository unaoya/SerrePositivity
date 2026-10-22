module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquarePrepend
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareCongr
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessRectangleTransport

/-!
概要：三経路 T・中央 V・S の逆による貼合せを、中央正方形の輪郭比較へ接続する。
方針：輪郭二重経路に T を前置し、S の逆と S の厳密 affine 相殺を照合する。
規約：輸送の二つの元の合成を結ぶ実経路。使われ方：Γ の右合成の貼合せ計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessRectangle
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q : W ⟶ B} {x y a₀ a₁ b₀ b₁ : W ⟶ algebra B N}
  {v : RelativeWitness q N a₀ b₀} {w : RelativeWitness q N a₁ b₁}
  {l : RelativeWitness q N a₀ a₁} {r : RelativeWitness q N b₀ b₁}
  (h : RelativeWitnessRectangle v w l r)
  (t : RelativeWitness q N x a₀) (s : RelativeWitness q N y b₀)

/-- 三経路貼合せの後に S,R を続けたものを、T,L,W に比較する実 class 二重経路。 -/
def glueContourSquare : RelativeWitnessSquare (q := q) (N := N) (a := x) (b := b₁)
    (((t.comp v).comp s.reverse).comp (s.comp r)) (t.comp (l.comp w)) := by
  have hv : (t.comp (v.comp r)).hom =
      (((t.comp v).comp s.reverse).comp (s.comp r)).hom := by
    apply Mon.Hom.ext
    simp only [RelativeWitness.comp_hom_linear, RelativeWitness.reverse_hom_linear]
    abel
  exact RelativeWitnessSquare.replacePaths (h.contourSquare.prepend t) hv rfl

end SquareZero.RelativeWitnessRectangle
namespace SquareZeroExtension
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} (N : Bimod B B)
  {q : W ⟶ B} {x y a₀ a₁ b₀ b₁ : W ⟶ SquareZero.algebra B N}
  {v : SquareZero.RelativeWitness q N a₀ b₀} {w : SquareZero.RelativeWitness q N a₁ b₁}
  {l : SquareZero.RelativeWitness q N a₀ a₁} {r : SquareZero.RelativeWitness q N b₀ b₁}
  (h : SquareZero.RelativeWitnessRectangle v w l r)
  (t : SquareZero.RelativeWitness q N x a₀) (s : SquareZero.RelativeWitness q N y b₀)

/-- 三経路貼合せと元の四辺から、輸送合成の実経路を得る。 -/
def glueContourTransportHomotopy : DGAlgebra.Path.Witness R
    (((transport N t ≫ transport N v) ≫ transport N s.reverse) ≫
      (transport N s ≫ transport N r))
    (transport N t ≫ (transport N l ≫ transport N w)) := by
  let z : DGAlgebra.Path.Witness R
      (transport N (((t.comp v).comp s.reverse).comp (s.comp r)))
      (transport N (t.comp (l.comp w))) :=
    transportHomotopy N (h.glueContourSquare t s)
  refine ⟨z.hom, ?_, ?_⟩
  · exact z.source_eq.trans (by simp only [← transport_comp])
  · exact z.target_eq.trans (by simp only [← transport_comp])

end SquareZeroExtension
end SerrePositivity.KST.LocalizingInvariants
