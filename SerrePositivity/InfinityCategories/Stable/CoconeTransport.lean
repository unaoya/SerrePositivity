module
public import SerrePositivity.InfinityCategories.Stable.CoconeLastVertex
public import SerrePositivity.InfinityCategories.Core.PrismContraction

/-! # 頂点を固定した余錐の逆向きの輸送

概要：図式の辺に沿って、その終点の余錐を頂点を固定したまま始点へ移せる。
方針：頂点上の slice の right fibration 性で最後の端点から prism を持ち上げる。
規約：この段階は辺の輸送の存在であり、cartesian 性の証明は別である。
使われ方：余錐の制限射の cartesian な輸送の構成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：最後の一次ホーンとパラメーターの包含は最後の prism 端点を経由する。
方針：ホーンの単体が値一に定値であることを使う。
規約：パラメーターは任意。使われ方：prism の終点を固定する持ち上げ。 -/
lemma stable_hornOneLast_inclusion (A : SSet.{u}) :
    ((horn 1 1).ι ▷ A) = snd (horn 1 1 : SSet.{u}) A ≫ prismEndpoint 1 A := by
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
lemma stable_rightFibration_lift_prism {E B : SSet.{u}} (p : E ⟶ B) [RightFibration p]
    (A : SSet.{u}) (f : A ⟶ E) (H : (Δ[1] : SSet.{u}) ⊗ A ⟶ B)
    (hH : prismEndpoint 1 A ≫ H = f ≫ p) :
    ∃ L : (Δ[1] : SSet.{u}) ⊗ A ⟶ E, prismEndpoint 1 A ≫ L = f ∧ L ≫ p = H := by
  have := rightAnodyneExtensions_point_whiskerRight A p (RightFibration.mem (p := p))
  have sq : CommSq (snd (horn 1 1 : SSet.{u}) A ≫ f) ((horn 1 1).ι ▷ A) p H := by
    constructor
    rw [stable_hornOneLast_inclusion, Category.assoc, Category.assoc, hH]
  refine ⟨sq.lift, ?_, sq.fac_right⟩
  have h := congrArg (fun q => hornOneLastSection A ≫ q) sq.fac_left
  simpa only [← Category.assoc, hornOneLastSection_ι, hornOneLastSection_snd,
    Category.id_comp] using h

/-- 概要：終点で指定した余錐を、図式の prism 全体へ頂点を固定して輸送できる。
方針：余錐を頂点上の slice への射とし、right fibration で prism を持ち上げる。
規約：図式と終点の余錐を厳密に保つ。cartesian 性はまだ含めない。
使われ方：余錐の制限射の辺の持ち上げ。 -/
lemma exists_cocone_fixedVertex_transport {K X : SSet.{u}} [Quasicategory X]
    (F : join K (Δ[0] : SSet.{u}) ⟶ X) (H : (Δ[1] : SSet.{u}) ⊗ K ⟶ X)
    (hH : prismEndpoint 1 K ≫ H = joinInl K Δ[0] ≫ F) :
    ∃ G : join ((Δ[1] : SSet.{u}) ⊗ K) Δ[0] ⟶ X,
      joinInl (Δ[1] ⊗ K) Δ[0] ≫ G = H ∧
      joinMap (prismEndpoint 1 K) (𝟙 Δ[0]) ≫ G = F ∧
      joinInr (Δ[1] ⊗ K) Δ[0] ≫ G = joinInr K Δ[0] ≫ F := by
  let z := joinInr K Δ[0] ≫ F
  let c := sliceOverCurry F (p := z) rfl
  have hcp : c ≫ sliceOverProjection z = joinInl K Δ[0] ≫ F := by
    rw [← sliceOverUncurry_projection, sliceOverUncurry_curry]
  obtain ⟨L, hL, hLp⟩ := stable_rightFibration_lift_prism (sliceOverProjection z) K c H
    (hH.trans hcp.symm)
  refine ⟨sliceOverUncurry L, ?_, ?_, sliceOverUncurry_fixed L⟩
  · rw [sliceOverUncurry_projection, hLp]
  · rw [← sliceOverUncurry_precomp, hL, sliceOverUncurry_curry]

end SerrePositivity.InfinityCategories
