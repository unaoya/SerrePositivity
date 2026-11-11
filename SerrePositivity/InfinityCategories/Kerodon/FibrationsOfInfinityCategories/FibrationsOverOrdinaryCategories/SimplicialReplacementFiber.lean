module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.TautScaffold
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.NerveFiber
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：simplicial replacement の fiber と taut scaffold の fiber 比較。
方針：定値の底の上の係数単体を取り出し、両構成の fiber を同じ係数値と同一視する。
規約：係数の Kan 性や底の充填性は不要。
使われ方：Kerodon Example 5.3.4.15（Tag 026E）、taut scaffold の fiber 同型。

対応節は Kerodon 5.3（Tag 035A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories

/-- 概要：係数値から定値の底の上の simplicial replacement への包含。
方針：底を定値射列とし、元の係数単体をそのまま添える。
規約：単体は Yoneda の射で表示する。
使われ方：Kerodon Construction 5.3.2.1（Tag 035V）、fiber 同型の順方向。 -/
def simplicialReplacementConstantLift {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : F.obj c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacement F where
  app d := ↾fun s ↦ ⟨(CategoryTheory.Functor.const (Fin (d.unop.len + 1))).obj c,
    SSet.yonedaEquiv.symm s⟩
  naturality d e α := by
    apply ConcreteCategory.hom_ext
    intro s
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    change SSet.yonedaEquiv.symm ((F.obj c).map α s) =
      stdSimplex.map α.unop ≫ SSet.yonedaEquiv.symm s ≫ F.map (𝟙 c)
    rw [F.map_id, Category.comp_id]
    exact (SSet.yonedaEquiv_symm_naturality_left (X := F.obj c) α.unop s).symm

/-- 概要：係数値の標準包含は底で指定の頂点に定値。
方針：射列が定値であることを定義から読む。
規約：底の頂点は nerveVertex c。
使われ方：Kerodon Remark 5.3.2.3（Tag 035X）、fiber への持ち上げ条件。 -/
lemma simplicialReplacementConstantLift_projection {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    simplicialReplacementConstantLift F c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F =
      SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) := rfl

/-- 概要：係数値から simplicial replacement の頂点 fiber への標準射。
方針：定値の底への標準包含を fiber へ持ち上げる。
規約：底の頂点を厳密に固定する。
使われ方：Kerodon Remark 5.3.2.3（Tag 035X）、fiber による係数値の回収。 -/
def simplicialReplacementFiberMap {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    F.obj c ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (simplicialReplacementConstantLift F c)
    (simplicialReplacementConstantLift_projection F c)

/-- 概要：simplicial replacement の標準 fiber 比較は同型。
方針：各次数で底の定値条件を代入し、Yoneda の全単射を用いる。
規約：厳密な単体集合の同型を得る。
使われ方：Kerodon Remark 5.3.2.3（Tag 035X）、taut scaffold の fiber 比較の始域。 -/
instance simplicialReplacementFiberMap_isIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : IsIso (simplicialReplacementFiberMap F c) := by
  rw [NatTrans.isIso_iff_isIso_app]
  rintro ⟨⟨n⟩⟩
  rw [isIso_iff_bijective]
  constructor
  · intro s t h
    have ht := eq_of_heq (Sigma.mk.inj (congrArg Subtype.val h)).2
    exact SSet.yonedaEquiv.symm.injective ht
  · rintro ⟨⟨σ, τ⟩, hσ⟩
    change σ = (CategoryTheory.Functor.const (Fin (n + 1))).obj c at hσ
    subst σ
    refine ⟨SSet.yonedaEquiv τ, ?_⟩
    apply Subtype.ext
    refine Sigma.ext (by rfl) ?_
    apply heq_of_eq
    exact SSet.yonedaEquiv.symm_apply_apply τ

/-- 概要：taut scaffold は係数値からの標準包含と可換。
方針：定値射列では輸送が恒等射になり、初区間への制限だけが残る。
規約：同一視を介さず元の単体集合への射の等式として述べる。
使われ方：Kerodon Example 5.3.4.15（Tag 026E）、fiber 比較が係数値の恒等に対応する計算。 -/
lemma simplicialReplacementConstantLift_tautScaffold {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) :
    simplicialReplacementConstantLift F c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveConstantLift F c := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  refine Sigma.ext (by rfl) ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext i
  change stdSimplex.map (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplexPrefixInclusion i.val n.unop.len _) ≫
      SSet.yonedaEquiv.symm s ≫ F.map (𝟙 c) = _
  rw [F.map_id, Category.comp_id]
  rfl

/-- 概要：taut scaffold が誘導する頂点 fiber 間の射。
方針：元の fiber の包含に taut scaffold を合成して標的の fiber に持ち上げる。
規約：両側で同じ底の頂点を固定する。
使われ方：Kerodon Example 5.3.4.15（Tag 026E）、taut scaffold の fiber ごとの比較。 -/
def tautScaffoldFiberMap {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) (c : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.simplicialReplacementProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) ⟶
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveProjection F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F) (by
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold_projection, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp])

/-- 概要：taut scaffold の fiber 射と係数値からの標準比較は可換。
方針：fiber の包含を後合成し、定値包含に関する計算へ帰着する。
規約：fiber の固定条件の証明には依存しない。
使われ方：Kerodon Example 5.3.4.15（Tag 026E）、fiber 射の同型性の計算。 -/
lemma simplicialReplacementFiberMap_tautScaffoldFiberMap
    {C : Type u} [Category.{u} C] (F : C ⥤ SSet.{u}) (c : C) :
    simplicialReplacementFiberMap F c ≫ tautScaffoldFiberMap F c = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberMap F c := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext
  change simplicialReplacementConstantLift F c ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.tautScaffold F = _
  exact simplicialReplacementConstantLift_tautScaffold F c

/-- 概要：taut scaffold の fiber 射は同型。
方針：係数値との両側の標準同型を可換式に代入する。
規約：全空間の同値はこの fiber ごとの同型性だけからは主張しない。
使われ方：Kerodon Example 5.3.4.15（Tag 026E）、taut scaffold の fiber 条件。 -/
@[kerodon 026E]
instance tautScaffoldFiberMap_isIso {C : Type u} [Category.{u} C]
    (F : C ⥤ SSet.{u}) (c : C) : IsIso (tautScaffoldFiberMap F c) := by
  have h := simplicialReplacementFiberMap_tautScaffoldFiberMap F c
  have he : tautScaffoldFiberMap F c =
      inv (simplicialReplacementFiberMap F c) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.weightedNerveFiberMap F c := by
    rw [← h, IsIso.inv_hom_id_assoc]
  rw [he]
  infer_instance

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
