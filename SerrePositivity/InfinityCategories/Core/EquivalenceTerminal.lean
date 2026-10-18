module

public import SerrePositivity.InfinityCategories.Core.FullyFaithful
public import SerrePositivity.InfinityCategories.Core.HomotopyBoundaryExtension
public import SerrePositivity.InfinityCategories.Core.KanHomotopyEquivalence

/-!
概要：quasicategory の同値による終対象の保存と反映。
方針：逆射で境界を充填し、可逆な二胞体に沿って元の境界へ戻す。
規約：同値は A3a の明示的な二胞体を持つ同値。
使われ方：HTT §1.2.12–1.2.13、Kerodon §4.8.4、§7.1。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：quasicategory の同値は終対象を終対象に送る。
方針：逆射で移した境界を既知の終対象で充填し、逆合成の可逆二胞体で移送する。
規約：境界の最後の頂点の条件を保つ。
使われ方：HTT §1.2.12、Kerodon §7.1 の終対象の同値不変性。 -/
lemma QCatEquivalence.map_isTerminalVertex {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) {x : X _⦋0⦌}
    (hx : IsTerminalVertex x) : IsTerminalVertex (e.hom.app (Opposite.op ⦋0⦌) x) := by
  intro n b hb
  have hi := FunctorIso.app e.homInvIso x
  have hterm : IsTerminalVertex (e.inv.app (Opposite.op ⦋0⦌)
      (e.hom.app (Opposite.op ⦋0⦌) x)) := hx.of_vertexIso hi.symm
  have hb' : boundaryVertex n (Fin.last (n + 1)) ≫ (b ≫ e.inv) =
      SSet.yonedaEquiv.symm (e.inv.app (Opposite.op ⦋0⦌)
        (e.hom.app (Opposite.op ⦋0⦌) x)) := by
    rw [← Category.assoc, hb, SSet.yonedaEquiv_symm_comp]
  obtain ⟨F, hF⟩ := hterm n (b ≫ e.inv) hb'
  have hF' : (boundary (n + 1)).ι ≫ (F ≫ e.hom) = b ≫ (e.inv ≫ e.hom) := by
    rw [← Category.assoc, hF, Category.assoc]
  have he : FunctorIso (b ≫ (e.inv ≫ e.hom)) b := by
    simpa only [Category.comp_id] using FunctorIso.precomp e.invHomIso b
  exact FunctorIso.exists_boundaryFilling he ⟨F ≫ e.hom, hF'⟩

/-- 概要：quasicategory の同値は終対象性を保ち反映する。
方針：逆同値で終対象性を戻し、単位の頂点での同型で元の頂点へ移す。
規約：任意の頂点 x を扱う。
使われ方：HTT §1.2.12、Kerodon §7.1 の終対象の同値不変性。 -/
lemma QCatEquivalence.isTerminalVertex_iff {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) (x : X _⦋0⦌) :
    IsTerminalVertex x ↔ IsTerminalVertex (e.hom.app (Opposite.op ⦋0⦌) x) := by
  constructor
  · exact e.map_isTerminalVertex
  · intro h
    exact (e.symm.map_isTerminalVertex h).of_vertexIso (FunctorIso.app e.homInvIso x)

/-- 概要：quasicategory の同値は可縮な Kan 複体であることを保つ。
方針：全頂点の終対象性を同値と本質的全射性で移し、全境界の充填に戻す。
規約：可縮性は A3d の全境界による条件。
使われ方：Kerodon §4.8.3–4.8.4 の写像空間の可縮性。 -/
lemma QCatEquivalence.isContractibleKan {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) (hX : IsContractibleKan X) :
    IsContractibleKan Y := by
  apply isContractibleKan_of_nonempty_of_all_terminal
  · obtain ⟨x⟩ := hX.nonempty
    exact ⟨e.hom.app (Opposite.op ⦋0⦌) x⟩
  · intro y
    obtain ⟨x, ⟨hi⟩⟩ := e.isEssentiallySurjective y
    exact (e.map_isTerminalVertex (hX.isTerminalVertex x)).of_vertexIso hi

/-- 概要：quasicategory の同値な対象の可縮 Kan 性は同値。
方針：同値と逆同値で可縮性を移す。
規約：両対象を quasicategory とする。
使われ方：Kerodon §4.8.3–4.8.4 の可縮性の不変性。 -/
lemma QCatEquivalence.isContractibleKan_iff {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (e : QCatEquivalence X Y) :
    IsContractibleKan X ↔ IsContractibleKan Y :=
  ⟨e.isContractibleKan, e.symm.isContractibleKan⟩

/-- 概要：Kan 複体間の単体的ホモトピー同値は可縮性を保ち反映する。
方針：Kan 複体の quasicategory の同値との比較を使う。
規約：両対象の Kan 性を明示する。
使われ方：Kerodon §4.8.3 の写像空間による終対象性の反映。 -/
lemma IsSimplicialHomotopyEquivalence.isContractibleKan_iff {X Y : SSet.{u}}
    [KanComplex X] [KanComplex Y] {f : X ⟶ Y} (hf : IsSimplicialHomotopyEquivalence f) :
    IsContractibleKan X ↔ IsContractibleKan Y :=
  hf.isQCatEquivalence.choose.isContractibleKan_iff

/-- 概要：写像空間で充満忠実な射は終対象性を反映する。
方針：像の終対象への写像空間の可縮性をホモトピー同値で戻し、A3d の判定を使う。
規約：本質的全射性はこの方向には不要。
使われ方：Kerodon §4.8.3、§7.1 の充満忠実な部分圏での終対象。 -/
lemma IsFullyFaithful.reflects_isTerminalVertex {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {f : X ⟶ Y} (hf : IsFullyFaithful f)
    {x : X _⦋0⦌} (hx : IsTerminalVertex (f.app (Opposite.op ⦋0⦌) x)) : IsTerminalVertex x := by
  apply isTerminalVertex_of_pinchedHom_isContractibleKan
  intro z
  exact (hf z x).isContractibleKan_iff.mpr
    (hx.pinchedHom_isContractibleKan (f.app (Opposite.op ⦋0⦌) z))

end SerrePositivity.InfinityCategories
