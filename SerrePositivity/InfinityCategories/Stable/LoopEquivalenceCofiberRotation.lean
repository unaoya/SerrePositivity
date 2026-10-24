module
public import SerrePositivity.InfinityCategories.Stable.LoopZeroOuterSpanColimit
public import SerrePositivity.InfinityCategories.Stable.CofiberRotationFromFiniteColimits

/-!
概要：実 loop 同値だけから、既存の cofiber 列の回転長方形を作る。
方針：外側 span の両終点が零であることを使い、既存の懸垂余極限を付加する。
規約：有限余極限や一般安定性を入力しない。
使われ方：一般零角の判定と、零 cofiber からの可逆性の検出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：任意の実 cofiber 列を同じ元の面のまま回転できる。
方針：二つの零終点を持つ外側 span の余極限を全長方形へ延長する。
規約：全 cofiber の存在や有限余極限は仮定しない。
使われ方：loop 同値から一般の fiber/cofiber 判定への接続。 -/
lemma nonempty_cofiberRotationRectangle_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [HasZeroVertex X] [HasFiniteLimits X]
    (s : X ⟶ loopDiagrams X) (hs : s ≫ loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : IsQCatEquivalence (s ≫ loopDiagramEvaluation X 0 0))
    (t : ZeroTriangle X) (ht : IsCofiberSequence t) :
    Nonempty (CofiberRotationRectangle t) := by
  let z := chosenZeroVertex X
  obtain ⟨τ, hτ, hlast⟩ :=
    exists_terminalCompositeTriangle z.isTerminal (squareBottomArrow t.square)
  have h : squareBottomEdge ≫ t.square = stdSimplex.δ (2 : Fin 3) ≫ τ := by
    rw [hτ, squareBottomArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply _).symm
  let G := pastingCornerGlue t.square τ h
  let p := pastingOuterBaseToCorner ≫ G
  let k := pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι
  have := pastingOuterBaseRestrict_standardSpan_trivialKanFibration p
  have h₁ : horn₂₀.ι₀₁ ≫ (k ≫ p) = stdSimplex.δ (1 : Fin 3) ≫ τ := by
    change horn₂₀.ι₀₁ ≫ ((pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι) ≫
      (pastingOuterBaseToCorner ≫ G)) = _
    calc
      _ = (horn₂₀.ι₀₁ ≫ (pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι ≫
          pastingOuterBaseToCorner)) ≫ G := by simp only [Category.assoc]
      _ = _ := by rw [pastingOuterStandardSpan_bottomEdge,
        Category.assoc, pastingCornerGlue_bottom]
  have h₂ : horn₂₀.ι₀₂ ≫ (k ≫ p) = squareLeftEdge ≫ t.square := by
    change horn₂₀.ι₀₂ ≫ ((pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι) ≫
      (pastingOuterBaseToCorner ≫ G)) = _
    calc
      _ = (horn₂₀.ι₀₂ ≫ (pastingOuterSpanIso.hom ≫ pastingOuterSpan.ι ≫
          pastingOuterBaseToCorner)) ≫ G := by simp only [Category.assoc]
      _ = _ := by rw [pastingOuterStandardSpan_leftEdge,
        Category.assoc, pastingCornerGlue_left]
  have hp : HasColimit p := by
    apply (hasColimit_iff_of_trivialRestriction p k).mpr
    apply hasColimit_zeroOuterSpan_of_loopEquivalence s hs hΩ
    change IsZeroVertex ((horn₂₀.ι₀₁ ≫ (k ≫ p)).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ∧
      IsZeroVertex ((horn₂₀.ι₀₂ ≫ (k ≫ p)).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    rw [h₁, h₂]
    constructor
    · change IsZeroVertex (τ.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (2 : Fin 3)))
      rw [hlast]
      exact z.isZero
    · exact t.zero_corner
  obtain ⟨d, hd⟩ := hp
  obtain ⟨F, hleft, hbottom, hright, _⟩ :=
    exists_pushoutRectangle_of_left_and_bottom t.square τ h ht d hd
  have houter : IsPushoutSquare (pastingSquare F 1) := by
    apply isPushoutSquare_pasting F _ hright
    rw [hleft]
    exact ht
  refine ⟨⟨F, hleft, ?_, hright, houter⟩⟩
  change IsZeroVertex ((pastingBottomTriangle F).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (2 : Fin 3)))
  rw [hbottom, hlast]
  exact z.isZero

end SerrePositivity.InfinityCategories
