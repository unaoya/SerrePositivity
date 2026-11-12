module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PreorderNerveHornExtension
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldFiniteCollapse
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianEdge

/-!
概要：有限鎖から区間への射の最初の辺の cocartesian 性。
方針：外側ホーンの頂点列を延長し、二次元で欠ける順序を時刻一の条件から補う。
規約：有限鎖の最初の辺は零頂点から一頂点への順序射。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、区間上の比較の cocartesian 辺の条件。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：標準単体への射は二次元以上の任意のホーンへの制限で決まる。
方針：標的を薄い圏の nerve に同型で移して頂点による外延性を使う。
規約：標的の次元とホーンの次元は独立。
使われ方：Kerodon §5.1.1（Tag 01T4）、底を固定した外側ホーンの充填。 -/
lemma stdSimplex_hom_ext_horn (n r : ℕ) (i : Fin (n + 3))
    {f g : (Δ[n + 2] : SSet.{u}) ⟶ Δ[r]}
    (h : (horn (n + 2) i).ι ≫ f = (horn (n + 2) i).ι ≫ g) : f = g := by
  apply (cancel_mono (stdSimplex.isoNerve r).hom).1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.thinNerve_hom_ext_horn n i
  simpa only [← Category.assoc] using congrArg (fun q ↦ q ≫ (stdSimplex.isoNerve r).hom) h

/-- 概要：有限鎖の最初の辺を一単体として表す。
方針：零から一への順序射を長さ一の射列とする。
規約：最初の辺の向きは零から一。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、区間への射の cocartesian 辺。 -/
def scaffoldFiniteInitialEdge (n : ℕ) : (nerve (ULift.{u} (Fin (n + 2)))) _⦋1⦌ :=
  ComposableArrows.mk₁ (homOfLE (show (ULift.up (0 : Fin (n + 2)) : ULift.{u} _) ≤
    ULift.up 1 from Fin.zero_le _))

/-- 概要：底を保つホーンの射の各頂点は区間の単体の対応する値に写る。
方針：ホーンの標準頂点で可換性を評価し、Yoneda 表示で底の値を読む。
規約：ホーンの次元は m+2。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、二次元の外側ホーンの不足した順序関係。 -/
lemma scaffoldFiniteCollapse_horn_vertex (n m : ℕ) (i : Fin (m + 3))
    (a : (horn (m + 2) i : SSet.{u}) ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (b : (Δ[m + 2] : SSet.{u}) ⟶ Δ[1])
    (sq : CommSq a (horn (m + 2) i).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n) b) (j : Fin (m + 3)) :
    (if (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.preorderNerveHornVertex a j).down = 0 then (0 : Fin 2) else 1) =
      (SSet.yonedaEquiv b) j := by
  let v : (horn (m + 2) i : SSet.{u}) _⦋0⦌ :=
    ⟨stdSimplex.obj₀Equiv.symm j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertex_mem_horn m i _⟩
  have he := congrArg (fun q ↦ q.app (Opposite.op ⦋0⦌) v) sq.w
  have he0 := congrArg (fun s : (Δ[1] : SSet.{u}) _⦋0⦌ ↦ s 0) he
  change (if (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.preorderNerveHornVertex a j).down = 0 then (0 : Fin 2) else 1) =
    (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm j)) 0 at he0
  have hb : (b.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm j)) 0 =
      (SSet.yonedaEquiv b) j := by
    conv_lhs => rw [← SSet.yonedaEquiv.symm_apply_apply b]
    rfl
  exact he0.trans hb

/-- 概要：最初の辺を固定した外側ホーンの頂点列は単調。
方針：三次元以上では全ての辺を使い、二次元では一頂点の正値性を底の区間から得る。
規約：最初の辺は有限鎖の零から一への辺。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、最初の辺の cocartesian 性の充填。 -/
lemma scaffoldFiniteInitialHorn_monotone (n m : ℕ)
    (a : (horn (m + 2) 0 : SSet.{u}) ⟶ nerve (ULift.{u} (Fin (n + 2))))
    (b : (Δ[m + 2] : SSet.{u}) ⟶ Δ[1])
    (he : a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge m) = scaffoldFiniteInitialEdge n)
    (sq : CommSq a (horn (m + 2) 0).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n) b) :
    Monotone (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.preorderNerveHornVertex a) := by
  cases m with
  | succ m =>
    intro j k hjk
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.preorderNerveHornVertex_le a j k hjk (Finset.card_le_three.trans (by omega))
  | zero =>
    have hp := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.preorderNerveHornVertex_edge_objs a 0 1 (Fin.zero_le _) (by simp)
    change (a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge 0)).obj 0 = _ ∧
      (a.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge 0)).obj 1 = _ at hp
    rw [he] at hp
    have hv1 : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.preorderNerveHornVertex a 1 = ULift.up (1 : Fin (n + 2)) := hp.2.symm
    have h10 : (1 : Fin (n + 2)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      change (1 : ℕ) = 0 at this
      contradiction
    have h1 := scaffoldFiniteCollapse_horn_vertex n 0 0 a b sq 1
    rw [hv1] at h1
    simp only [ite_eq_right h10] at h1
    have h2 := scaffoldFiniteCollapse_horn_vertex n 0 0 a b sq 2
    have hv2 : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.preorderNerveHornVertex a 2).down ≠ 0 := by
      intro hz
      have hb : (1 : Fin 2) ≤ (SSet.yonedaEquiv b) 2 := by
        rw [h1]
        exact (stdSimplex.objEquiv (SSet.yonedaEquiv b)).toOrderHom.monotone (by decide)
      rw [hz, ite_eq_left rfl] at h2
      rw [← h2] at hb
      exact (by decide : ¬ (1 : Fin 2) ≤ 0) hb
    apply Fin.monotone_iff_le_succ.mpr
    intro j
    fin_cases j
    · exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.preorderNerveHornVertex_le a 0 1 (Fin.zero_le _) (by simp)
    · change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.preorderNerveHornVertex a 1 ≤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.preorderNerveHornVertex a 2
      rw [hv1]
      change 1 ≤ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.preorderNerveHornVertex a 2).down.val
      have hz : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.preorderNerveHornVertex a 2).down.val ≠ 0 := fun h ↦ hv2 (Fin.ext h)
      omega

/-- 概要：有限鎖の最初の辺は区間への射に関して cocartesian。
方針：外側ホーンの単調な頂点列を単体へ延長し、底の射の一意性で可換性を確認する。
規約：n=0 の場合も含む。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、区間上の scaffold 比較の辺の条件。 -/
lemma scaffoldFiniteInitialEdge_isCocartesian (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse.{u} n) (scaffoldFiniteInitialEdge n) := by
  intro m a b he sq
  obtain ⟨l, hl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.preorderNerveHorn_extend a (scaffoldFiniteInitialHorn_monotone n m a b he sq)
  refine CommSq.HasLift.mk' { l := l, fac_left := hl, fac_right := ?_ }
  apply stdSimplex_hom_ext_horn m 1 0
  rw [← Category.assoc, hl]
  exact sq.w

/-- 概要：標準区間からの最初の辺の射は指定した最初の一単体を表す。
方針：長さ一の射列の両対象と射を比較する。
規約：二点鎖の nerve への標準同型を使う。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、円柱の辺の表示の整合性。 -/
lemma scaffoldFiniteInitialEdge_yoneda (n : ℕ) :
    SSet.yonedaEquiv ((stdSimplex.isoNerve.{u} 1).hom ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge n)) =
      scaffoldFiniteInitialEdge n := by
  apply ComposableArrows.ext₁
  case left =>
    apply ULift.ext
    apply Fin.ext
    rfl
  case right =>
    apply ULift.ext
    apply Fin.ext
    change 1 = (1 : Fin (n + 2)).val
    simp
  case w => exact Subsingleton.elim _ _

/-- 概要：left fibration の最初の辺上の辺は区間への合成に関して cocartesian。
方針：left fibration の全辺の cocartesian 性と最初の辺の cocartesian 性を合成する。
規約：射の像が有限鎖の最初の一単体であることを要求する。
使われ方：Kerodon Theorem 5.3.5.7（Tag 037Q）、円柱の各垂直辺の条件。 -/
lemma scaffoldFiniteInitialEdge_comp_isCocartesian (n : ℕ) {E : SSet.{u}}
    (p : E ⟶ nerve (ULift.{u} (Fin (n + 2)))) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (e : E _⦋1⦌) (he : p.app (Opposite.op ⦋1⦌) e = scaffoldFiniteInitialEdge n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (p ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteCollapse n) e := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCocartesianEdge_of_leftFibration p e).comp
  rw [he]
  exact scaffoldFiniteInitialEdge_isCocartesian n

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
