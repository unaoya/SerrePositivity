module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessRectangleBoundary
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeTransportHomotopy

/-!
概要：動く四辺の class 正方形を、元の輸送射の二つの実合成を結ぶ経路へ移す。
方針：輪郭の固定端点二重経路と輸送の厳密合成則を組み合わせる。
規約：同じ相対模型の二脚を保つ。使われ方：Γ の実合成比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} (N : Bimod B B)
  {q : W ⟶ B} {a b c : W ⟶ SquareZero.algebra B N}

lemma transport_comp (v : SquareZero.RelativeWitness q N a b)
    (w : SquareZero.RelativeWitness q N b c) :
    transport N v ≫ transport N w = transport N (v.comp w) := by
  apply DGAlgebra.RelativeHomotopyPullback.hom_ext R (SquareZero.projection B N)
    c (SquareZero.zeroSection B N)
  · change (_ ≫ _) ≫ relativeLeft N c = _ ≫ relativeLeft N c
    rw [Category.assoc, transport_left, transport_left, transport_left]
  · change (_ ≫ _) ≫ relativeRight N c = _ ≫ relativeRight N c
    rw [Category.assoc, transport_right, transport_right, transport_right]
  · change (_ ≫ _) ≫ relativePath N c = _ ≫ relativePath N c
    apply Mon.Hom.ext
    rw [transport_path_linear_precomp N w (transport N v)]
    simp only [← Category.assoc, transport_left]
    rw [transport_path_linear N v, transport_path_linear N (v.comp w)]
    simp only [Mon.comp_hom', SquareZero.RelativeWitness.comp_hom_linear,
      comp_add, comp_sub, Category.assoc]
    abel

variable {a₀ a₁ b₀ b₁ : W ⟶ SquareZero.algebra B N}
  {v : SquareZero.RelativeWitness q N a₀ b₀} {w : SquareZero.RelativeWitness q N a₁ b₁}
  {l : SquareZero.RelativeWitness q N a₀ a₁} {r : SquareZero.RelativeWitness q N b₀ b₁}
  (s : SquareZero.RelativeWitnessRectangle v w l r)

/-- 輪郭の二つの元の輸送合成を結ぶ実乗法的経路。 -/
def contourTransportHomotopy : DGAlgebra.Path.Witness R
    (transport N v ≫ transport N r) (transport N l ≫ transport N w) := by
  let h : DGAlgebra.Path.Witness R (transport N (v.comp r)) (transport N (l.comp w)) :=
    transportHomotopy N s.contourSquare
  refine ⟨h.hom, ?_, ?_⟩
  · exact h.source_eq.trans (transport_comp N v r).symm
  · exact h.target_eq.trans (transport_comp N l w).symm

lemma contourTransportHomotopy_left : (contourTransportHomotopy N s).hom ≫
    DGAlgebra.Path.map R (relativeLeft N b₁) =
      relativeLeft N a₀ ≫ DGAlgebra.Path.diagonal R W := by
  change (transportHomotopy (v := v.comp r) (w := l.comp w) N s.contourSquare).hom ≫ _ = _
  exact transportHomotopy_left N s.contourSquare

lemma contourTransportHomotopy_right : (contourTransportHomotopy N s).hom ≫
    DGAlgebra.Path.map R (relativeRight N b₁) =
      relativeRight N a₀ ≫ DGAlgebra.Path.diagonal R B := by
  change (transportHomotopy (v := v.comp r) (w := l.comp w) N s.contourSquare).hom ≫ _ = _
  exact transportHomotopy_right N s.contourSquare

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
