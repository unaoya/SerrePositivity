module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoreCoconeLeg

/-! # 脚の合成二単体を点下の余錐の辺に戻す

概要：二つの余錐の指定脚と頂点の辺の合成二単体から、その脚の余錐の族を作る。
方針：標準二単体を点と区間の join へ戻し、両端と共通右辺を計算する。
規約：入力の二単体をそのまま使う。使われ方：二点図式の余錐間の射の持ち上げ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：脚と頂点の辺の合成二単体を、点と区間の join からの族として表す。
方針：標準 join 同型の後に二単体を合成する。
規約：追加の仮定は不要。使われ方：二本の脚の族の貼り合わせ。 -/
def coconeLegTriangle {K X : SSet.{u}} {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    {i : (Δ[0] : SSet.{u}) ⟶ K}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) c.vertex d.vertex}
    (t : (c.leg i).CompStruct e (d.leg i)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u}) Δ[1] ⟶ X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom ≫ SSet.yonedaEquiv.symm t.simplex

/-- 概要：脚の合成二単体の族の右辺は指定された頂点の辺。
方針：右包含が二単体の面 δ₀ であることを使う。
規約：射の厳密な等号。使われ方：二つの脚の族の共通辺。 -/
lemma coconeLegTriangle_right {K X : SSet.{u}} {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    {i : (Δ[0] : SSet.{u}) ⟶ K}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) c.vertex d.vertex}
    (t : (c.leg i).CompStruct e (d.leg i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{u}) Δ[1] ≫ coconeLegTriangle t = SSet.yonedaEquiv.symm e.edge := by
  change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom ≫ SSet.yonedaEquiv.symm t.simplex) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_inr]
  apply SSet.yonedaEquiv.injective
  rw [stdSimplex.yonedaEquiv_δ_comp]
  exact (congrArg (fun a => X.δ 0 a) (SSet.yonedaEquiv.apply_symm_apply t.simplex)).trans
    (t.d₀.trans (SSet.yonedaEquiv.apply_symm_apply e.edge).symm)

/-- 概要：脚の合成二単体の族の始点は最初の余錐の指定脚。
方針：面 δ₂ と join の端点包含を照合する。
規約：余錐の脚の実際の射を保つ。使われ方：貼り合わせた辺の始点。 -/
lemma coconeLegTriangle_zero {K X : SSet.{u}} {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    {i : (Δ[0] : SSet.{u}) ⟶ K}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) c.vertex d.vertex}
    (t : (c.leg i).CompStruct e (d.leg i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ (1 : Fin 2)) ≫ coconeLegTriangle t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 (Δ[0] : SSet.{u})) ≫ c.val := by
  have hf : stdSimplex.δ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm t.simplex =
      SSet.yonedaEquiv.symm (c.leg i).edge := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun a => X.δ 2 a) (SSet.yonedaEquiv.apply_symm_apply t.simplex)).trans
      (t.d₂.trans (SSet.yonedaEquiv.apply_symm_apply (c.leg i).edge).symm)
  change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom ≫ SSet.yonedaEquiv.symm t.simplex) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_vertex_one]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ (2 : Fin 3)) ≫ _ = _
  rw [Category.assoc, hf]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫ c.val)) = _
  rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]

/-- 概要：脚の合成二単体の族の終点は次の余錐の指定脚。
方針：面 δ₁ と join の端点包含を照合する。
規約：余錐の脚の実際の射を保つ。使われ方：貼り合わせた辺の終点。 -/
lemma coconeLegTriangle_one {K X : SSet.{u}} {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    {i : (Δ[0] : SSet.{u}) ⟶ K}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) c.vertex d.vertex}
    (t : (c.leg i).CompStruct e (d.leg i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (𝟙 (Δ[0] : SSet.{u})) (stdSimplex.δ (0 : Fin 2)) ≫ coconeLegTriangle t =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 (Δ[0] : SSet.{u})) ≫ d.val := by
  have hf : stdSimplex.δ (1 : Fin 3) ≫ SSet.yonedaEquiv.symm t.simplex =
      SSet.yonedaEquiv.symm (d.leg i).edge := by
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp]
    exact (congrArg (fun a => X.δ 1 a) (SSet.yonedaEquiv.apply_symm_apply t.simplex)).trans
      (t.d₁.trans (SSet.yonedaEquiv.apply_symm_apply (d.leg i).edge).symm)
  change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 1).hom ≫ SSet.yonedaEquiv.symm t.simplex) = _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_vertex_one]
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ stdSimplex.δ (1 : Fin 3)) ≫ _ = _
  rw [Category.assoc, hf]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm
    (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫ d.val)) = _
  rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]

/-- 概要：脚の合成二単体の族は左の固定頂点を変えない。
方針：始点での脚の一致を左包含で制限する。
規約：図式の指定点の射を保持する。使われ方：coslice の固定条件。 -/
lemma coconeLegTriangle_fixed {K X : SSet.{u}} {p : K ⟶ X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    {i : (Δ[0] : SSet.{u}) ⟶ K}
    {e : SSet.Truncated.Edge (X := (truncation 2).obj X) c.vertex d.vertex}
    (t : (c.leg i).CompStruct e (d.leg i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[1] ≫ coconeLegTriangle t = i ≫ p := by
  have h := congrArg (fun a => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{u}) Δ[0] ≫ a) (coconeLegTriangle_zero t)
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.id_comp,
    ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, c.property] at h
  exact h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
