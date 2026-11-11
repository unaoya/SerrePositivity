module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.UpperMissingCylinder
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HollowCube

/-!
概要：指定座標の上面を一つ欠く立方体の正確な所属条件と Kan 延長。
方針：元の包含順序・座標分離を保ち、Λ[1,0] を使う空洞柱へ移す。
規約：下面は全て既知、合成面は指定点以外。使われ方：外側ホーンの端点 Hom の延長。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra SSet

open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
variable {T : Type u}

/-- Λ[1,0] の単体は全頂点で座標零となるもの。 -/
lemma mem_lowerEndpoint_iff {n : SimplexCategoryᵒᵖ} (s : (Δ[1] : SSet.{u}).obj n) :
    s ∈ (Λ[1, (0 : Fin 2)] : (Δ[1] : SSet.{u}).Subcomplex).obj n ↔
      ∀ t, s.down.toOrderHom t = 0 := by
  rcases n with ⟨⟨n⟩⟩
  rw [SSet.mem_horn_iff_notMem_range]
  constructor
  · rintro ⟨j, hj, h⟩ t
    fin_cases j
    · exact False.elim (hj rfl)
    · have ht : s.down.toOrderHom t ≠ 1 := fun ht ↦ h ⟨t, ht⟩
      by_cases hz : s.down.toOrderHom t = 0
      · exact hz
      · exact False.elim (ht (Fin.eq_last_of_not_lt (by simpa using hz)))
  · intro h
    refine ⟨1, by decide, ?_⟩
    rintro ⟨t, ht⟩
    change s.down.toOrderHom t = 1 at ht
    exact (by decide : (0 : Fin 2) ≠ 1) ((h t).symm.trans ht)

/-- 指定座標の上面一つを欠く、元の立方体境界。 -/
def upperMissingCube (i : T) : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).Subcomplex :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinder (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeBoundary {x : T // x ≠ i})).preimage (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeSplit i)

/-- 既知部分は一定の零座標面、または指定外の一定の一座標面に属する単体。 -/
lemma mem_upperMissingCube_iff (i : T) {n : SimplexCategoryᵒᵖ} (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).obj n) :
    F ∈ (upperMissingCube i).obj n ↔
      (∃ x, ∀ t, x ∉ F.obj t) ∨ ∃ x, x ≠ i ∧ ∀ t, x ∈ F.obj t := by
  classical
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeSplit i).app n F ∈
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinder (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeBoundary {x : T // x ≠ i})).obj n ↔ _
  rw [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinder, SSet.Subcomplex.mem_unionProd_iff, mem_lowerEndpoint_iff]
  change (∀ t, ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeCoordinateMap i).app n F).down.toOrderHom t = 0) ∨
    (∃ x : {x : T // x ≠ i}, (∀ t, x.1 ∈ F.obj t) ∨ ∀ t, x.1 ∉ F.obj t) ↔ _
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeCoordinateMap_apply, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeCoordinate, OrderHom.coe_mk,
    h10, ite_eq_right_iff, imp_false]
  constructor
  · rintro (h | ⟨x, h | h⟩)
    · exact Or.inl ⟨i, h⟩
    · exact Or.inr ⟨x.1, x.2, h⟩
    · exact Or.inl ⟨x.1, h⟩
  · rintro (⟨x, h⟩ | ⟨x, hx, h⟩)
    · by_cases hx : x = i
      · exact Or.inl (hx ▸ h)
      · exact Or.inr ⟨⟨x, hx⟩, Or.inr h⟩
    · exact Or.inr ⟨⟨x, hx⟩, Or.inl h⟩

/-- 同じ座標分離で、上面を欠く立方体を空洞柱へ同型で移す。 -/
def upperMissingCubeIso (i : T) :
    (upperMissingCube i : SSet.{u}) ≅ _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinder (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeBoundary {x : T // x ≠ i}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.subcomplexPreimageIso (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeSplitIso i)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinder (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeBoundary {x : T // x ≠ i}))

/-- 上面を一つ欠く元の立方体の包含は anodyne。 -/
lemma upperMissingCube_anodyne (i : T) : SSet.anodyneExtensions (upperMissingCube i).ι := by
  let e : Arrow.mk (upperMissingCube i).ι ≅
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinder (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeBoundary {x : T // x ≠ i})).ι :=
    Arrow.isoMk (upperMissingCubeIso i) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cubeSplitIso i) (by rfl)
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff e).mpr (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.upperMissingCylinder_anodyne _)

/-- 最後の集合の欠けた点、または最初の集合の指定外の点で所属を判定する。 -/
lemma mem_upperMissingCube_endpoints_iff (i : T) {n : SimplexCategoryᵒᵖ}
    (F : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T).obj n) :
    F ∈ (upperMissingCube i).obj n ↔
      (∃ x, x ∉ F.obj (Fin.last n.unop.len)) ∨ ∃ x, x ≠ i ∧ x ∈ F.obj 0 := by
  rw [mem_upperMissingCube_iff]
  constructor
  · rintro (⟨x, hx⟩ | ⟨x, hxi, hx⟩)
    · exact Or.inl ⟨x, hx _⟩
    · exact Or.inr ⟨x, hxi, hx 0⟩
  · rintro (⟨x, hx⟩ | ⟨x, hxi, hx⟩)
    · exact Or.inl ⟨x, fun t ht ↦ hx ((F.map (homOfLE (Fin.le_last t))).le ht)⟩
    · exact Or.inr ⟨x, hxi, fun t ↦ (F.map (homOfLE (Fin.zero_le t))).le hx⟩

/-- 上面を一つ欠く元の立方体上の写像を、Kan 複体内で延長する。 -/
lemma upperMissingCube_extension (i : T) {X : SSet.{u}} [KanComplex X]
    (f : (upperMissingCube i : SSet) ⟶ X) :
    ∃ g : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.cube T ⟶ X, (upperMissingCube i).ι ≫ g = f := by
  have : HasLiftingProperty (upperMissingCube i).ι (terminal.from X) :=
    upperMissingCube_anodyne i _ (by rwa [← fibration_iff])
  let sq : CommSq f (upperMissingCube i).ι (terminal.from X) (terminal.from _) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
