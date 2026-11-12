module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CocartesianFixedVertexTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeTerminalExtension
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ConeTerminalBoundary

/-!
概要：cocartesian fibration の fiber の終対象から相対境界充填を得る。
方針：最後の頂点を固定して境界を終点の fiber へ輸送し、そこで充填して prism で戻す。
規約：元・標的は quasicategory、モデル構造は用いない。
使われ方：Kerodon Proposition 7.1.5.19（Tag 02WU） の終対象の場合と §7.1.6 の錐。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：cocartesian fibration の fiber の終対象は元の射に関して終点境界を充填する。
方針：基底の標準単体を最後の頂点へ収縮し、終対象を固定した輸送、fiber の充填、逆向きの prism の延長を組み合わせる。
規約：元・標的は quasicategory、p は cocartesian fibration。
使われ方：Kerodon Proposition 7.1.5.19（Tag 02WU） の相対終対象への接続。 -/
lemma terminalBoundaryLifting_of_isTerminalVertex_fiber {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p]
    (b₀ : B _⦋0⦌) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b₀) _⦋0⦌) (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x.val := by
  intro n a b hend sq
  let i : (Δ[0] : SSet.{u}) ⟶ (boundary (n + 1) : SSet.{u}) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1))
  haveI : Mono i := by
    rw [NatTrans.mono_iff_mono_app]
    intro d
    obtain ⟨⟨d⟩⟩ := d
    rw [mono_iff_injective]
    intro s t _
    apply stdSimplex.ext
    intro j
    apply Fin.ext
    have hs := (s j).isLt
    have ht := (t j).isLt
    omega
  have hxb : p.app (Opposite.op ⦋0⦌) x.val = b₀ := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero] using x.property
  have hlastb : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫ b =
      SSet.yonedaEquiv.symm b₀ := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι, Category.assoc, ← sq.w, ← Category.assoc, hend,
      SSet.yonedaEquiv_symm_comp, hxb]
  have hlastb₀ : b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) = b₀ := by
    have h := congrArg SSet.yonedaEquiv hlastb
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h
  let β := (Δ[1] ◁ (boundary (n + 1)).ι) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction (n + 1) ≫ b
  have hβ₀ : a ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ β := by
    dsimp [β]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n + 1]), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_zero, Category.id_comp]
    exact sq.w
  have hβi : (Δ[1] ◁ i) ≫ β = SSet.const (p.app (Opposite.op ⦋0⦌) x.val) := by
    dsimp [β, i]
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_lastVertex,
      SSet.const_comp, hlastb₀, hxb]
  obtain ⟨H, hHi, hH₀, hHp, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cocartesianHomotopy_exists_fixed_vertex p i a x.val hend β hβ₀ hβi
  have hH₁p : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary (n + 1) : SSet.{u}) ≫ H) ≫ p = SSet.const b₀ := by
    rw [Category.assoc, hHp]
    dsimp [β]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[n + 1]), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_one,
      SSet.const_comp, hlastb₀, SSet.comp_const]
  let f₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift p b₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary (n + 1) : SSet.{u}) ≫ H) hH₁p
  have hf₁ : i ≫ f₁ = SSet.yonedaEquiv.symm x := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext p b₀
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, ← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality,
      Category.assoc, hHi, SSet.comp_const, SSet.yonedaEquiv_symm_comp]
    rw [SSet.yonedaEquiv_symm_zero]
    rfl
  obtain ⟨L, hL⟩ := hx n f₁ hf₁
  let F₁ := L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b₀
  have hF₁ : (boundary (n + 1)).ι ≫ F₁ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary (n + 1) : SSet.{u}) ≫ H := by
    dsimp [F₁]
    rw [← Category.assoc, hL]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hF₁p : F₁ ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[n + 1] ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction (n + 1) ≫ b) := by
    dsimp [F₁]
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_one, SSet.const_comp, hlastb₀]
  have hHlast : H.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismBoundaryLastVerticalEdge n) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x.val 1 := by
    let v : ((Δ[1] : SSet.{u}) ⊗ Δ[0]) _⦋1⦌ :=
      ⟨SSet.yonedaEquiv (𝟙 Δ[1]), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) 1⟩
    have hv : (Δ[1] ◁ i).app (Opposite.op ⦋1⦌) v = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismBoundaryLastVerticalEdge n := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        apply stdSimplex.ext
        intro j
        rfl
    have hh := ConcreteCategory.congr_hom (NatTrans.congr_app hHi (Opposite.op ⦋1⦌)) v
    change H.app (Opposite.op ⦋1⦌) ((Δ[1] ◁ i).app (Opposite.op ⦋1⦌) v) = _ at hh
    rw [hv] at hh
    exact hh
  have hHinv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismBoundaryLastVerticalEdge n))) := by
    rw [hHlast]
    have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isEquivalencePathVertex_const x.val
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsEquivalencePathVertex at hi
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge_functorVertex] at hi
    exact hi
  obtain ⟨G, hG, hG₁, hGp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prism_lift_boundary_with_final_endpoint p n H F₁
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction (n + 1) ≫ b) hF₁ hHp hF₁p hHinv
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n + 1] ≫ G, ?_, ?_⟩
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hG, hH₀]
  · rw [Category.assoc, hGp, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_zero, Category.id_comp]

/-- 概要：cocartesian fibration の fiber の終対象性は元の射の相対終点境界充填と同値。
方針：fiber への制限と cocartesian な輸送による逆向きを組み合わせる。
規約：元・標的は quasicategory、p は cocartesian fibration。
使われ方：Kerodon Proposition 7.1.5.19（Tag 02WU） の終対象の場合。 -/
lemma isTerminalVertex_fiber_iff_terminalBoundaryLifting {E B : SSet.{u}}
    [Quasicategory E] [Quasicategory B] (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p]
    (b : B _⦋0⦌) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting p x.val :=
  ⟨terminalBoundaryLifting_of_isTerminalVertex_fiber p b x,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting.isTerminalVertex_fiber p b x⟩

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
