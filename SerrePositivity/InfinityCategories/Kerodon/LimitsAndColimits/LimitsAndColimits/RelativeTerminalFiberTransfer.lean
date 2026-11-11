module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CocartesianTerminalBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.VertexFiberMap

/-!
概要：共通の底への cocartesian 輸送を保つ射では、fiber の相対終対象性を全空間へ移せる。
方針：境界と標的の単体を最後の fiber へ同時輸送し、fiber で充填して prism で戻す。
規約：対象の射自身には inner fibration 性だけを仮定する。
使われ方：Kerodon Proposition 7.1.5.19（Tag 02WU） の双対による相対 join の充填。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：fiber の射に関する終点境界充填は共通の底への輸送を使って全空間へ移る。
方針：終点を固定して境界を輸送し、その像を延長して fiber の充填と接合する。
規約：両射影は cocartesian な輸送を持ち、f はその辺を保つ inner fibration。
使われ方：反転により fiber の相対始対象から全空間の相対始対象を得る。 -/
lemma kanTerminalBoundaryLifting_of_fiber_map {E F B : SSet.{u}}
    [Quasicategory E] [Quasicategory F] [Quasicategory B]
    (p : E ⟶ B) (q : F ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration p] [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianHornFibration q]
    (f : E ⟶ F) [InnerFibration f] (hf : f ≫ q = p)
    (hpres : ∀ e : E _⦋1⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p e →
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge q (f.app (Opposite.op ⦋1⦌) e))
    (b₀ : B _⦋0⦌) (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b₀) _⦋0⦌)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b₀) x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalBoundaryLifting f x.val := by
  intro n a b hend sq
  let i : (Δ[0] : SSet.{u}) ⟶ (boundary (n + 1) : SSet.{u}) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1))
  have : Mono i := by
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
  have hlastb : SSet.yonedaEquiv.symm (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) ≫ b ≫ q =
      SSet.yonedaEquiv.symm b₀ := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι, Category.assoc, ← Category.assoc (boundary (n + 1)).ι b q,
      ← sq.w, Category.assoc a f q, hf, ← Category.assoc, hend,
      SSet.yonedaEquiv_symm_comp, hxb]
  have hlastb₀ : (b ≫ q).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (Fin.last (n + 1))) = b₀ := by
    have h := congrArg SSet.yonedaEquiv hlastb
    simpa only [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply] using h
  let β := (Δ[1] ◁ (boundary (n + 1)).ι) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction (n + 1) ≫ b ≫ q
  have hβ₀ : a ≫ p = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ β := by
    dsimp [β]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc,
      ← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n + 1]), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_zero, Category.id_comp]
    rw [← hf, ← Category.assoc, sq.w, Category.assoc]
  have hβi : (Δ[1] ◁ i) ≫ β = SSet.const (p.app (Opposite.op ⦋0⦌) x.val) := by
    dsimp [β, i]
    rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex_ι,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_lastVertex,
      SSet.const_comp, hlastb₀, hxb]
  obtain ⟨H, hHi, hH₀, hHp, hHc⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cocartesianHomotopy_exists_fixed_vertex p i a x.val hend β hβ₀ hβi
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
  have hHf : (H ≫ f) ≫ q = (Δ[1] ◁ (boundary (n + 1)).ι) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction (n + 1) ≫ b ≫ q) := by
    rw [Category.assoc, hf, hHp]
  have hHfc (y : (boundary (n + 1) : SSet.{u}) _⦋0⦌) :
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.HasCocartesianHornLifting q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex ((H ≫ f).app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 Δ[1]), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y 1))) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_hasCocartesianHornLifting q _).1
    apply hpres
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_iff_hasCocartesianHornLifting p _).2 (hHc y)
  have hHf₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ (H ≫ f) =
      (boundary (n + 1)).ι ≫ b := by
    rw [← Category.assoc, hH₀, sq.w]
  have hb₀ : b ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n + 1] ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction (n + 1) ≫ b ≫ q) := by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_zero, Category.id_comp]
  obtain ⟨J, hJ, hJ₀, hJq, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cocartesianHomotopy_extend q (boundary (n + 1)).ι
    (H ≫ f) b (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction (n + 1) ≫ b ≫ q) hHf₀ hb₀ hHf hHfc
  have hJ₁q : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[n + 1] ≫ J) ≫ q = SSet.const b₀ := by
    rw [Category.assoc, hJq, ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prismLastContraction_one,
      SSet.const_comp, hlastb₀]
  let g₁ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift q b₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[n + 1] ≫ J) hJ₁q
  have hs₁ : CommSq f₁ (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap p q f hf b₀) g₁ := by
    constructor
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext q b₀
    dsimp only [f₁, g₁]
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι]
    rw [← Category.assoc (boundary (n + 1)).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[n + 1]) J,
      ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hJ]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, Category.assoc]
  obtain ⟨L, hL, hLf⟩ := hx n f₁ g₁ hf₁ hs₁
  let F₁ := L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι p b₀
  have hF₁ : (boundary (n + 1)).ι ≫ F₁ =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (boundary (n + 1) : SSet.{u}) ≫ H := by
    dsimp [F₁]
    rw [← Category.assoc, hL]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  have hF₁f : F₁ ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 Δ[n + 1] ≫ J := by
    have h := hLf =≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι q b₀
    simpa only [F₁, g₁, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι] using h
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
  obtain ⟨G, hG, hG₁, hGp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.prism_lift_boundary_with_final_endpoint f n H F₁ J
    hF₁ hJ.symm hF₁f hHinv
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n + 1] ≫ G, ?_, ?_⟩
  · rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, hG, hH₀]
  · rw [Category.assoc, hGp, hJ₀]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
