module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismContraction
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RightPrism
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Slice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.SliceMap

/-! # 頂点を固定した余錐の逆向きの輸送

概要：図式の辺に沿って、その終点の余錐を頂点を固定したまま始点へ移せる。
方針：頂点上の slice の right fibration 性で最後の端点から prism を持ち上げる。
規約：この段階は辺の輸送の存在であり、cartesian 性の証明は別である。
使われ方：余錐の制限射の cartesian な輸送の構成。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：最後の一次ホーンとパラメーターの包含は最後の prism 端点を経由する。
方針：ホーンの単体が値一に定値であることを使う。
規約：パラメーターは任意。使われ方：prism の終点を固定する持ち上げ。 -/
lemma stable_hornOneLast_inclusion (A : SSet.{u}) :
    ((horn 1 1).ι ▷ A) = snd (horn 1 1 : SSet.{u}) A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, a⟩
  apply Prod.ext
  · apply stdSimplex.ext
    intro j
    change s.val j = 1
    obtain ⟨v, hv, hm⟩ := (mem_horn_iff_notMem_range s.val (1 : Fin 2)).1 s.property
    have hv0 : v = 0 := by fin_cases v <;> simp_all
    subst v
    have hs : s.val j ≠ 0 := fun h => hm ⟨j, h⟩
    apply Fin.ext
    have hlt := (s.val j).isLt
    have hne : (s.val j).val ≠ 0 := fun h => hs (Fin.ext h)
    omega
  · rfl

/-- 概要：right fibration に沿って最後の端点を固定した prism を持ち上げられる。
方針：最後の一次ホーンとパラメーターの積の right anodyne 性を使う。
規約：元・標的の quasicategory 性は不要。使われ方：固定頂点の余錐の輸送。 -/
lemma stable_rightFibration_lift_prism {E B : SSet.{u}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p]
    (A : SSet.{u}) (f : A ⟶ E) (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ H = f ≫ p) :
    ∃ L : (Δ[1] : SSet.{u}) ⊗ A ⟶ E, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ L = f ∧ L ≫ p = H := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightAnodyneExtensions_point_whiskerRight A p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem (p := p))
  have sq : CommSq (snd (horn 1 1 : SSet.{u}) A ≫ f) ((horn 1 1).ι ▷ A) p H := by
    constructor
    rw [stable_hornOneLast_inclusion, Category.assoc, Category.assoc, hH]
  refine ⟨sq.lift, ?_, sq.fac_right⟩
  have h := congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneLastSection A ≫ q) sq.fac_left
  simpa only [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneLastSection_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneLastSection_snd,
    Category.id_comp] using h

/-- 概要：終点で指定した余錐を、図式の prism 全体へ頂点を固定して輸送できる。
方針：余錐を頂点上の slice への射とし、right fibration で prism を持ち上げる。
規約：図式と終点の余錐を厳密に保つ。cartesian 性はまだ含めない。
使われ方：余錐の制限射の辺の持ち上げ。 -/
lemma exists_cocone_fixedVertex_transport {K X : SSet.{u}} [Quasicategory X]
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}) ⟶ X) (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ X)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K ≫ H = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ F) :
    ∃ G : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((Δ[1] : SSet.{u}) ⊗ K) Δ[0] ⟶ X,
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[1] ⊗ K) Δ[0] ≫ G = H ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 K) (𝟙 Δ[0]) ≫ G = F ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[1] ⊗ K) Δ[0] ≫ G = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫ F := by
  let z := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫ F
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry F (p := z) rfl
  have hcp : c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection z = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K Δ[0] ≫ F := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry]
  obtain ⟨L, hL, hLp⟩ := stable_rightFibration_lift_prism (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection z) K c H
    (hH.trans hcp.symm)
  refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry L, ?_, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed L⟩
  · rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, hLp]
  · rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, hL, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
