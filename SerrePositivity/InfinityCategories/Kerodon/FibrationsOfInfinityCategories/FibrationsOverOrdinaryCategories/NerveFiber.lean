module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.Nerve
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：weighted nerve の頂点 fiber と係数の値の厳密な同型。
方針：一定の底の上では初区間の図式が最後の標準単体からの射で一意に決まることを使う。
規約：係数の値に Kan 性は要求しない。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve が係数の値を fiber に持つことの検査。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：係数の n 単体を一定の底の上の初区間の図式に展開する。
方針：各 i 単体は初区間の包含 Δ[i]→Δ[n] で制限して作る。
規約：底の射列は c に定値。
使われ方：Kerodon Definition 5.3.3.1（Tag 025X）、weighted nerve の fiber の包含。 -/
def weightedNerveConstantDiagram {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) {n : ℕ} (s : (F.obj c) _⦋n⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixWeight n ⟶ (CategoryTheory.Functor.const (Fin (n + 1))).obj c ⋙ F where
  app i := stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)) ≫
    SSet.yonedaEquiv.symm s
  naturality i j f := by
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val j.val (leOfHom f)) ≫
        (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion j.val n (Nat.le_of_lt_succ j.isLt)) ≫
          SSet.yonedaEquiv.symm s) =
      (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n (Nat.le_of_lt_succ i.isLt)) ≫
        SSet.yonedaEquiv.symm s) ≫ F.map (𝟙 c)
    rw [CategoryTheory.Functor.map_id, Category.comp_id, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_comp]

/-- 概要：係数の値を一定の底の上の weighted nerve に写す。
方針：一定の合成可能射列に、各単体から作る初区間の図式を添える。
規約：c における値の全次数を扱う単体集合の射。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve の頂点 fiber の明示的な包含。 -/
def weightedNerveConstantLift {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) (c : C) :
    F.obj c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerve F where
  app d := ↾fun s ↦ ⟨(CategoryTheory.Functor.const (Fin (d.unop.len + 1))).obj c,
    weightedNerveConstantDiagram F c s⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro s
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply NatTrans.ext
    funext i
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val e.unop.len _) ≫
        SSet.yonedaEquiv.symm ((F.obj c).map α s) =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction α.unop i) ≫
        (stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion (α.unop.toOrderHom i).val d.unop.len _) ≫
          SSet.yonedaEquiv.symm s)
    have hy : SSet.yonedaEquiv.symm ((F.obj c).map α s) =
        stdSimplex.map α.unop ≫ SSet.yonedaEquiv.symm s :=
      (SSet.yonedaEquiv_symm_naturality_left (X := F.obj c) α.unop s).symm
    rw [hy, ← Category.assoc,
      ← CategoryTheory.Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixRestriction_factor,
      CategoryTheory.Functor.map_comp, Category.assoc]

/-- 概要：一定の底への weighted nerve の包含は底で c に定値。
方針：定値関手が c の nerve の定値単体であることを計算する。
規約：底の頂点は nerveVertex c。
使われ方：Kerodon §5.3.3（Tag 025W）、係数の値を weighted nerve の fiber へ持ち上げる条件。 -/
lemma weightedNerveConstantLift_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    weightedNerveConstantLift F c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) := by
  rfl

/-- 概要：係数の値から weighted nerve の頂点 fiber への標準射。
方針：一定の底の上の包含を fiber へ持ち上げる。
規約：射影を厳密に固定する。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve の fiber 比較の順方向。 -/
def weightedNerveFiberMap {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) (c : C) :
    F.obj c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (weightedNerveConstantLift F c) (weightedNerveConstantLift_projection F c)

/-- 概要：weighted nerve の標準 fiber 比較は厳密な同型。
方針：各次数で、最後の成分による単射性と自然性による全射性を確認する。
規約：F の値の充填性は不要。
使われ方：Kerodon §5.3.3（Tag 025W）、weighted nerve の fiber による係数の値の回収。 -/
instance weightedNerveFiberMap_isIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : IsIso (weightedNerveFiberMap F c) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  constructor
  · intro s t h
    have hτ := eq_of_heq (Sigma.mk.inj (congrArg Subtype.val h)).2
    have hh := congrArg (fun τ ↦ τ.app (Fin.last n)) hτ
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n n _) ≫ SSet.yonedaEquiv.symm s =
      stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion n n _) ≫ SSet.yonedaEquiv.symm t at hh
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion_id, CategoryTheory.Functor.map_id, Category.id_comp] at hh
    exact SSet.yonedaEquiv.symm.injective hh
  · rintro ⟨⟨σ, τ⟩, hσ⟩
    change σ = (CategoryTheory.Functor.const (Fin (n + 1))).obj c at hσ
    subst σ
    refine ⟨SSet.yonedaEquiv (τ.app (Fin.last n)), ?_⟩
    apply Subtype.ext
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    apply NatTrans.ext
    funext i
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n _) ≫
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (τ.app (Fin.last n))) = τ.app i
    rw [Equiv.symm_apply_apply]
    have ht := τ.naturality (homOfLE (Fin.le_last i))
    change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n _) ≫ τ.app (Fin.last n) =
      τ.app i ≫ F.map (𝟙 c) at ht
    have hid : F.map (𝟙 c) = 𝟙 (F.obj c) := F.map_id c
    rw [hid] at ht
    exact ht.trans (Category.comp_id (τ.app i))

/-- 概要：係数の値と weighted nerve の頂点 fiber の明示的な同型。
方針：標準 fiber 比較の各次数の全単射性から逆を取る。
規約：同値だけでなく単体集合の厳密な同型。
使われ方：Kerodon §5.3.3（Tag 025W）、Kan 値 weighted nerve の fiber の Kan 性。 -/
noncomputable def weightedNerveFiberIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : F.obj c ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) :=
  asIso (weightedNerveFiberMap F c)

/-- 概要：Kan な係数値に対応する weighted nerve の頂点 fiber は Kan 複体。
方針：係数値との同型でホーンを移して充填し、逆の同型で戻す。
規約：指定した対象 c における Kan 性だけを仮定する。
使われ方：Kerodon §5.3.3（Tag 025W）、strict transport の weighted nerve の fiber 比較。 -/
instance weightedNerveFiber_kanComplex {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) [KanComplex (F.obj c)] :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) := by
  let e := weightedNerveFiberIso F c
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
  intro n i _ a
  obtain ⟨H, hH⟩ := KanComplex.hornFilling (a ≫ e.inv)
  refine ⟨H ≫ e.hom, ?_⟩
  rw [← Category.assoc, ← hH, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
