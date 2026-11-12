module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopZeroOuterSpanColimit
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationFromFiniteColimits

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
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：任意の実 cofiber 列を同じ元の面のまま回転できる。
方針：二つの零終点を持つ外側 span の余極限を全長方形へ延長する。
規約：全 cofiber の存在や有限余極限は仮定しない。
使われ方：loop 同値から一般の fiber/cofiber 判定への接続。 -/
lemma nonempty_cofiberRotationRectangle_of_loopEquivalence {X : SSet.{u}}
    [Quasicategory X] [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.HasZeroVertex X] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits X]
    (s : X ⟶ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagrams X) (hs : s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 1 1 = 𝟙 X)
    (hΩ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (s ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.loopDiagramEvaluation X 0 0))
    (t : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.ZeroTriangle X) (ht : _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsCofiberSequence t) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CofiberRotationRectangle t) := by
  let z := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.chosenZeroVertex X
  obtain ⟨τ, hτ, hlast⟩ :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_terminalCompositeTriangle z.isTerminal (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow t.square)
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ t.square = stdSimplex.δ (2 : Fin 3) ≫ τ := by
    rw [hτ, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge]
    exact (SSet.yonedaEquiv.symm_apply_apply _).symm
  let G := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue t.square τ h
  let p := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ G
  let k := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι
  have := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseRestrict_standardSpan_trivialKanFibration p
  have h₁ : horn₂₀.ι₀₁ ≫ (k ≫ p) = stdSimplex.δ (1 : Fin 3) ≫ τ := by
    change horn₂₀.ι₀₁ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ G)) = _
    calc
      _ = (horn₂₀.ι₀₁ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι ≫
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner)) ≫ G := by simp only [Category.assoc]
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterStandardSpan_bottomEdge,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue_bottom]
  have h₂ : horn₂₀.ι₀₂ ≫ (k ≫ p) = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ t.square := by
    change horn₂₀.ι₀₂ ≫ ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι) ≫
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner ≫ G)) = _
    calc
      _ = (horn₂₀.ι₀₂ ≫ (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpanIso.hom ≫ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterSpan.ι ≫
          _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterBaseToCorner)) ≫ G := by simp only [Category.assoc]
      _ = _ := by rw [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingOuterStandardSpan_leftEdge,
        Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.pastingCornerGlue_left]
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.hasColimit_iff_of_trivialRestriction p k).mpr
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.hasColimit_zeroOuterSpan_of_loopEquivalence s hs hΩ
    change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((horn₂₀.ι₀₁ ≫ (k ≫ p)).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) ∧
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((horn₂₀.ι₀₂ ≫ (k ≫ p)).app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
    rw [h₁, h₂]
    constructor
    · change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex (τ.app (Opposite.op ⦋0⦌)
        (stdSimplex.obj₀Equiv.symm (2 : Fin 3)))
      rw [hlast]
      exact z.isZero
    · exact t.zero_corner
  obtain ⟨d, hd⟩ := hp
  obtain ⟨F, hleft, hbottom, hright, _⟩ :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.exists_pushoutRectangle_of_left_and_bottom t.square τ h ht d hd
  have houter : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingSquare F 1) := by
    apply _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isPushoutSquare_pasting F _ hright
    rw [hleft]
    exact ht
  refine ⟨⟨F, hleft, ?_, hright, houter⟩⟩
  change _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.IsZeroVertex ((_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.pastingBottomTriangle F).app (Opposite.op ⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (2 : Fin 3)))
  rw [hbottom, hlast]
  exact z.isZero

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
