module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianCosliceLifting
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone

/-! # 恒等射の余錐の普遍性
概要：可逆な射は点の coslice の始対象となり、恒等射は一点図式の余極限を与える。
方針：最初の外側ホーンの充填を coslice の境界の充填に移す。
規約：引用を証明に使わない。使われ方：第一行の退化した押し出し四角形。
原典：HTT §1.2.12・§4.3.2、BGT Lemma 7.3。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：点の coslice で可逆な射を表す頂点は始対象。
方針：外側ホーンの充填を、点への射の上の coslice の相対境界充填に適用する。
規約：C は quasicategory。使われ方：恒等余錐の普遍性。 -/
lemma isInitialVertex_pointCoslice_of_isInvertibleEdge {C : SSet.{u}} [Quasicategory C]
    (a : (Δ[0] : SSet.{u}) ⟶ C) (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder a) _⦋0⦌)
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge a t)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex t := by
  let p := terminal.from C
  have hcart : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianCosliceVertex a p t := by
    intro n σ β hσ hw
    obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hasInitialHornFillers_of_isInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge a t) ht n σ hσ
    exact ⟨F, hF, terminal.hom_ext _ _⟩
  intro n f hf
  let s := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p).app (Opposite.op ⦋0⦌) t
  have hw : f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp a p = (boundary (n + 1)).ι ≫ SSet.const s := by
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro v
    apply Subtype.ext
    exact terminal.hom_ext _ _
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianCosliceVertex a p (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n 0 ≫ f)) := by
    rw [hf, Equiv.apply_symm_apply]
    exact hcart
  obtain ⟨F, hF, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.exists_coslice_boundary_lift_of_cocartesian_vertex a p n f (SSet.const s) hw he
  exact ⟨F, hF⟩

/-- 概要：一点図式の恒等射を表す余錐。
方針：恒等辺を点の coslice の頂点にする。
規約：余錐の頂点も同じ一点。使われ方：恒等辺を持つ押し出しの基本場合。 -/
def identityCocone {C : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ C) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexOfEdge a (SSet.Truncated.Edge.id (X := (truncation 2).obj C) (SSet.yonedaEquiv a))

/-- 概要：一点図式の恒等余錐は余極限余錐。
方針：恒等辺がホモトピー圏で可逆であることから coslice の始対象性を使う。
規約：C は quasicategory。使われ方：退化した普遍四角形の構成。 -/
lemma identityCocone_isColimit {C : SSet.{u}} [Quasicategory C] (a : (Δ[0] : SSet.{u}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (identityCocone a) := by
  apply isInitialVertex_pointCoslice_of_isInvertibleEdge
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointCosliceVertexEdge_ofEdge a _)).2
  change IsIso (SSet.Truncated.HomotopyCategory.homMk (SSet.Truncated.Edge.id _))
  rw [SSet.Truncated.HomotopyCategory.homMk_id]
  infer_instance

/-- 概要：余錐の実際の射が等しければ余極限性も同じ。
方針：固定条件から基底の等号を復元し、部分型の等号に帰着する。
規約：基底図式が定義的に同じでなくてもよい。使われ方：退化余錐の同定。 -/
lemma isColimitCone_iff_of_map_eq {K C : SSet.{u}} {p q : K ⟶ C}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (h : c.val = d.val) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d := by
  have hp : p = q := by rw [← c.property, ← d.property, h]
  subst q
  have hd : c = d := Subtype.ext h
  subst d
  rfl

/-- 概要：恒等射の余錐はその頂点に定値な射で表される。
方針：恒等辺は零単体の退化であることを使う。
規約：点の射 a は任意。使われ方：退化四角形の余錐との比較。 -/
lemma identityCocone_val {C : SSet.{u}} (a : (Δ[0] : SSet.{u}) ⟶ C) :
    (identityCocone a).val = SSet.const (SSet.yonedaEquiv a) := by
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ SSet.yonedaEquiv.symm
    (SSet.Truncated.Edge.id (X := (truncation 2).obj C) (SSet.yonedaEquiv a)).edge = _
  have he : SSet.yonedaEquiv.symm
      (SSet.Truncated.Edge.id (X := (truncation 2).obj C) (SSet.yonedaEquiv a)).edge =
      (SSet.const (SSet.yonedaEquiv a) : (Δ[1] : SSet.{u}) ⟶ C) := by
    apply SSet.yonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one (SSet.yonedaEquiv a)).symm
  exact (congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ C =>
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).hom ≫ f) he).trans (SSet.comp_const _ _)

/-- 概要：一点図式の定値な余錐は余極限。
方針：恒等余錐と実際の射が一致することを使う。
規約：基底の表示を余錐の固定条件から回収する。
使われ方：終点で恒等となる余錐の普遍性。 -/
lemma pointCocone_isColimit_of_constant {C : SSet.{u}} [Quasicategory C]
    {p : (Δ[0] : SSet.{u}) ⟶ C} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (x : C _⦋0⦌)
    (hc : c.val = SSet.const x) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := by
  apply (isColimitCone_iff_of_map_eq c (identityCocone (SSet.yonedaEquiv.symm x)) ?_).2
    (identityCocone_isColimit _)
  rw [identityCocone_val, Equiv.apply_symm_apply]
  exact hc

end SerrePositivity.KST.SConstruction
