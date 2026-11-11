module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.SimplexVertexDetection
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TerminalUniqueness
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CosliceTriangleFiber

/-!
概要：標準区間の辺に付ける錐の一意性。
方針：join の頂点を左右に分け、左の終点から右の各頂点への辺の単調性を使う。
規約：区間の標準辺は恒等射、終点は一。
使われ方：Kerodon Proposition 5.1.3.11（Tag 01U8）、Proposition 5.1.6.7（Tag 01VB）、相対 coslice の基底条件の除去。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：標準単体への join の二射は両因子への制限で決まる。
方針：零単体の切断を零・一に分け、頂点による標準単体への射の検出を使う。
規約：左右の因子は任意の単体集合。
使われ方：Kerodon Proposition 5.1.3.11（Tag 01U8）、区間の錐の一意性。 -/
lemma join_hom_ext_stdSimplex_factors {K L : SSet.{u}} {n : ℕ}
    {f g : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K L ⟶ (Δ[n] : SSet.{u})}
    (hl : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K L ≫ g)
    (hr : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L ≫ f = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K L ≫ g) : f = g := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  rintro ⟨l, x, y⟩
  fin_cases l
  · exact congrArg (fun h ↦ h.app (Opposite.op ⦋0⦌) y) hr
  · exact congrArg (fun h ↦ h.app (Opposite.op ⦋0⦌) x) hl

/-- 概要：始点が一である区間内の辺は一への定値射。
方針：始点の値と単調性により両頂点が一になることを使う。
規約：始点は δ₁、値一は δ₀ によって指定する。
使われ方：Kerodon Proposition 5.1.3.11（Tag 01U8）、錐の右側の頂点の値の検出。 -/
lemma interval_hom_eq_const_one_of_source_one (e : (Δ[1] : SSet.{u}) ⟶ Δ[1])
    (he : stdSimplex.δ (1 : Fin 2) ≫ e = stdSimplex.δ (0 : Fin 2)) :
    e = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  have h0 : SSet.yonedaEquiv e 0 = 1 := by
    have hh := congrArg SSet.yonedaEquiv he
    rw [stdSimplex.yonedaEquiv_δ_comp] at hh
    exact congrArg (fun z : (Δ[1] : SSet.{u}) _⦋0⦌ ↦ z 0) hh
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro i
  change SSet.yonedaEquiv e i = 1
  have hm := (stdSimplex.objEquiv (SSet.yonedaEquiv e)).toOrderHom.monotone (Fin.zero_le i)
  change SSet.yonedaEquiv e 0 ≤ SSet.yonedaEquiv e i at hm
  rw [h0] at hm
  exact le_antisymm (Fin.le_last _) hm

/-- 概要：区間の標準辺を固定した join の錐は右因子を一へ送る。
方針：左因子の終点と右因子の各頂点の join を区間に移し、始点一の辺の定値性を使う。
規約：右因子 A は任意。
使われ方：Kerodon Proposition 5.1.3.11（Tag 01U8）、固定標準辺の coslice の基底の値。 -/
lemma join_interval_cone_inr_eq_const_one {A : SSet.{u}}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[1] : SSet.{u}) A ⟶ Δ[1])
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl Δ[1] A ≫ f = 𝟙 Δ[1]) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[1] A ≫ f = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.stdSimplex_hom_ext_vertices
  apply ConcreteCategory.hom_ext
  intro a
  let g : (Δ[1] : SSet.{u}) ⟶ Δ[1] := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (stdSimplex.δ (0 : Fin 2)) (SSet.yonedaEquiv.symm a) ≫ f
  have hg : stdSimplex.δ (1 : Fin 2) ≫ g = stdSimplex.δ (0 : Fin 2) := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inl]
    simp only [g, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl_joinMap, Category.assoc, hf, Category.comp_id]
  have ht : stdSimplex.δ (0 : Fin 2) ≫ g = SSet.yonedaEquiv.symm a ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[1] A ≫ f := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_zero_inr]
    simp only [g, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr_joinMap, Category.assoc]
  have hc := interval_hom_eq_const_one_of_source_one g hg
  have hh := congrArg SSet.yonedaEquiv ht
  rw [hc, SSet.comp_const, SSet.yonedaEquiv_const, SSet.yonedaEquiv_comp,
    Equiv.apply_symm_apply] at hh
  exact hh.symm

/-- 概要：標準区間の恒等射の coslice は各次数で高々一点。
方針：全ての錐は左で恒等、右で一への定値なので両因子上で一致する。
規約：任意の次数 m を扱う。
使われ方：Kerodon Proposition 5.1.3.11（Tag 01U8）、相対 coslice の基底条件の一意性。 -/
instance intervalIdentityCoslice_subsingleton (m : ℕ) :
    Subsingleton ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (𝟙 (Δ[1] : SSet.{u}))) _⦋m⦌) where
  allEq s t := by
    apply Subtype.ext
    apply join_hom_ext_stdSimplex_factors
    · exact s.property.trans t.property.symm
    · rw [join_interval_cone_inr_eq_const_one s.val s.property,
        join_interval_cone_inr_eq_const_one t.val t.property]

/-- 概要：標準区間の恒等射の coslice は一への定値射影を持つ。
方針：各錐の右因子への制限を計算し、Yoneda の評価を使う。
規約：射影の終域は標準区間。
使われ方：Kerodon Proposition 5.1.3.11（Tag 01U8）、三角形の基底の終点の固定。 -/
lemma intervalIdentityCoslice_projection : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (𝟙 (Δ[1] : SSet.{u})) =
    SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply SSet.hom_ext
  rintro ⟨⟨m⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr Δ[1] Δ[m] ≫ s.val) = _
  rw [join_interval_cone_inr_eq_const_one s.val s.property]
  rfl

/-- 概要：標準区間の恒等射に付ける標準的な錐。
方針：終点を重複させる退化二単体を、辺と点の join の表示に戻す。
規約：追加した点は時刻一。
使われ方：Kerodon Proposition 5.1.3.11（Tag 01U8）、相対 coslice の基底の錐の選択。 -/
def intervalIdentityCosliceVertex : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (𝟙 (Δ[1] : SSet.{u}))) _⦋0⦌ :=
  ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 1 0).hom ≫ stdSimplex.σ (1 : Fin 2), by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.joinStdSimplexIso_one_inl]
    apply SSet.yonedaEquiv.injective
    decide⟩

/-- 概要：標準区間の恒等射の coslice は全ての次数で非空。
方針：標準的な錐の定値単体を使う。
規約：その錐は一意でもある。
使われ方：Kerodon Proposition 5.1.3.11（Tag 01U8）、基底条件の補完。 -/
instance intervalIdentityCoslice_nonempty (m : ℕ) :
    Nonempty ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (𝟙 (Δ[1] : SSet.{u}))) _⦋m⦌) :=
  ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant intervalIdentityCosliceVertex m⟩

/-- 概要：標準単体内の図式に対し、終点を固定した錐は各次数で高々一点。
方針：固定した左図式と右因子の定値単体の一致から錐を検出する。
規約：固定する図式の形 K は任意。
使われ方：Kerodon Proposition 5.1.3.11（Tag 01U8）、相対 coslice の fiber 内の基底条件の一意性。 -/
instance stdSimplexCosliceFiber_subsingleton {K : SSet.{u}} {n : ℕ}
    (e : K ⟶ (Δ[n] : SSet.{u})) (y : (Δ[n] : SSet.{u}) _⦋0⦌) (m : ℕ) :
    Subsingleton ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection e) y) _⦋m⦌) where
  allEq s t := by
    apply Subtype.ext
    apply Subtype.ext
    apply join_hom_ext_stdSimplex_factors
    · exact s.val.property.trans t.val.property.symm
    · apply SSet.yonedaEquiv.injective
      exact s.property.trans t.property.symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
