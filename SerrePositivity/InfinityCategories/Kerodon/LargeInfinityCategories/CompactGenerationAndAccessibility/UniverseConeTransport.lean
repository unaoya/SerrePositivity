module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingConeShape
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.FactorizationSliceExtension

/-!
概要：小さい順序余錐の比較を実際の大きい図式の宇宙へ移す。
方針：join の宇宙同型の左因子に関する自然性を使う。
規約：元の形状同型と全包含を厳密に保持する。
使われ方：交互構成の閉前置段への形状輸送。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：余錐の宇宙同型は元の図式の射について自然。
方針：join 同型の二因子自然性と右標準単体の同型を合成する。
規約：全単体での厳密な等式。
使われ方：成分余錐と全余錐の比較の宇宙持ち上げ。 -/
lemma uliftCoconeShapeIso_hom_left {K L : SSet.{u}} (f : K ⟶ L) (n : ℕ) :
    (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[n])) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso L n).hom =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso K n).hom ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((SSet.uliftFunctor.{v, u}).map f) (𝟙 Δ[n]) := by
  unfold _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso
  simp only [Iso.trans_hom, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinIso, Iso.refl_hom]
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftJoinIso_hom_naturality]
  simp only [Category.assoc]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap_comp]
  rw [(SSet.uliftFunctor.{v, u}).map_id]
  simp only [Category.comp_id, Category.id_comp]

/-- 概要：余錐の宇宙同型の逆も元の図式の射について自然。
方針：順方向の自然性を同型の相殺で反転する。
規約：全単体での厳密な等式。
使われ方：大きい宇宙での閉前置段の成分制限。 -/
lemma uliftCoconeShapeIso_inv_left {K L : SSet.{u}} (f : K ⟶ L) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((SSet.uliftFunctor.{v, u}).map f) (𝟙 Δ[n]) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso L n).inv =
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso K n).inv ≫
        (SSet.uliftFunctor.{v, u}).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[n])) := by
  apply (cancel_epi (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso K n).hom).1
  rw [← Category.assoc, ← uliftCoconeShapeIso_hom_left, Category.assoc,
    Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]

/-- 概要：小さい余錐形状同型を大きい宇宙の余錐形状同型へ移す。
方針：標準単体付き join の宇宙同型の逆と持ち上げた元の同型を合成する。
規約：頂点の宇宙だけを変更する。
使われ方：全交互形状と現在成分形状の一頂点追加。 -/
def liftedCoconeIso {K L : SSet.{u}} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0] ≅ L) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join ((SSet.uliftFunctor.{v, u}).obj K) Δ[0] ≅
      (SSet.uliftFunctor.{v, u}).obj L :=
  (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCoconeShapeIso K 0).symm ≪≫ (SSet.uliftFunctor.{v, u}).mapIso e

/-- 概要：小さい余錐形状の可換四角形は持ち上げた余錐形状でも可換。
方針：左因子自然性と元の全射の等式を関手で移す。
規約：元の図式への射を保持する。
使われ方：現在成分の全図式の整合。 -/
lemma liftedCoconeIso_naturality {K L K' L' : SSet.{u}}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0] ≅ L) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K' Δ[0] ≅ L')
    (f : K ⟶ K') (g : L ⟶ L')
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap f (𝟙 Δ[0]) ≫ e'.hom = e.hom ≫ g) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap ((SSet.uliftFunctor.{v, u}).map f) (𝟙 Δ[0]) ≫
        (liftedCoconeIso e').hom =
      (liftedCoconeIso e).hom ≫ (SSet.uliftFunctor.{v, u}).map g := by
  simp only [liftedCoconeIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  rw [← Category.assoc, uliftCoconeShapeIso_inv_left, Category.assoc,
    ← Functor.map_comp, h, Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
