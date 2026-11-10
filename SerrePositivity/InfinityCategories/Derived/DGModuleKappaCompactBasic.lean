module
public import SerrePositivity.KST.NonConnective.DGKappaConeInput
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedZeroObjects
public import SerrePositivity.InfinityCategories.Derived.DGModuleNerveZero
public import SerrePositivity.InfinityCategories.F2.Compact.InitialCompact
public import SerrePositivity.InfinityCategories.F2.Compact.RepresentableRetractions
/-!
概要：実 dg 加群の同じ実導来頂点に対する、全 Hom の κ-compact 性の基本入口。
方針：K-7 正本の頂点を固定し、始対象・頂点同型・ホモトピー retract の一般判定を使う。
規約：ordinary compact や perfect で置換せず、添字宇宙 u と標的宇宙を分離する。
使われ方：D-8 c の零入力、選択代表の変更、perfect の retract 閉性への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open SerrePositivity.KST.NonConnective
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- 同じ実半自由分解への頂点における、元の全共変 Hom の κ-compact 性。 -/
abbrev dgModuleKappaCompact (κ : Cardinal.{u}) (M : ModuleCategory R D) : Prop :=
  F2.Compact.IsKappaCompact.{u, max (u + 1) v} κ (dgConeModuleDerivedVertex R D M)

/-- 実導来頂点が零である加群は、無限 κ について κ-compact。 -/
lemma dgModuleKappaCompact_of_isZero {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    {M : ModuleCategory R D} (hM : IsZeroVertex (dgConeModuleDerivedVertex R D M)) :
    dgModuleKappaCompact R D κ M :=
  F2.Compact.isKappaCompact_of_isInitialVertex hκ hM.1

/-- 元の零加群の同じ実導来頂点は κ-compact。 -/
lemma dgModuleKappaCompact_zero {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ) :
    dgModuleKappaCompact R D κ (moduleZero R D) := by
  apply dgModuleKappaCompact_of_isZero R D hκ
  apply dgModuleResolvedInfinity_preservesZeroVertices R (ModuleCategory R D) D
    (dgConeModuleForget R D)
  exact dgNerve_isZeroVertex_of_closed_isZero _ (moduleZero_isZero R D)

/-- 同じ実導来 ∞ 圏の頂点同型は κ-compact 性を保ち反映する。 -/
lemma dgModuleKappaCompact_iff_of_vertexIso {κ : Cardinal.{u}}
    {M N : ModuleCategory R D}
    (e : VertexIso (dgConeModuleDerivedVertex R D M) (dgConeModuleDerivedVertex R D N)) :
    dgModuleKappaCompact R D κ M ↔ dgModuleKappaCompact R D κ N :=
  F2.Compact.isKappaCompact_iff_of_iso e

/-- 元の h 圏内の retract により、同じ加群頂点の κ-compact 性を戻す。 -/
lemma dgModuleKappaCompact_of_vertexRetract {κ : Cardinal.{u}}
    {M N : ModuleCategory R D}
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsVertexRetractOf
      (dgConeModuleDerivedVertex R D M) (dgConeModuleDerivedVertex R D N))
    (hN : dgModuleKappaCompact R D κ N) : dgModuleKappaCompact R D κ M :=
  F2.Compact.IsKappaCompact.of_retract h hN

end SerrePositivity.InfinityCategories
