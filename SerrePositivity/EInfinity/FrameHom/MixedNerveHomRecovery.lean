module
public import SerrePositivity.EInfinity.FrameHom.MixedNerveNatTransFunctor
public import SerrePositivity.EInfinity.FrameHom.NerveColumnRoofNaturality
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomotopyClasses
/-! 概要：Hom 宇宙を上げた全通常円柱から元の混合宇宙円柱を回収する。
方針：元の up・down の厳密な逆性を全パラメータで使う。
規約：元の全図式と同じ自然変換を保持する。
使われ方：cofibrant 相対列の忘却像と元の複体屋根の接合。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.MixedNerve
open CategoryTheory SSet MonoidalCategory MonoidalClosed
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable (C : Type (u + 1)) [Category.{u} C]

/-- 概要：元の nerve の Hom 宇宙の往復は厳密に恒等。
方針：全単体列と元の射を比較する。
規約：対象と全射を保持。使われ方：元の全パラメータの回収。 -/
lemma down_up : down C ≫ up C = 𝟙 _ := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro Γ
  change (Γ ⋙ ULiftHom.down.{u, u + 1, u + 1}) ⋙ ULiftHom.up.{u, u + 1, u + 1} = Γ
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- 概要：同じ全円柱は Hom 宇宙を下げた全パラメータ上で厳密に回収される。
方針：元の円柱定義の up と down の往復を消去する。
規約：元の全自然変換を保持。使われ方：元の全導来屋根の比較。 -/
lemma homotopy_down_h {D : Type (u + 1)} [Category.{u} D] {F G : C ⥤ D} (a : F ⟶ G) :
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (liftedNatTrans a)).h ≫ down D =
      (down C ▷ (Δ[1] : SSet.{u + 1})) ≫ (homotopy a).h := by
  change _ = (down C ▷ (Δ[1] : SSet.{u + 1})) ≫
    ((up C ▷ (Δ[1] : SSet.{u + 1})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (liftedNatTrans a)).h ≫ down D)
  rw [← Category.assoc, ← comp_whiskerRight, down_up, id_whiskerRight, Category.id_comp]

/-- 概要：持ち上げた全通常射の像は元の混合円柱の全制限。
方針：元の down 回収式と同じ全前後合成公式を使う。
規約：全パラメータと端点表示を保持。使われ方：元の複体屋根の全回収。 -/
lemma liftedHom_postcomp_arrow {D : Type (u + 1)} [Category.{u} D]
    {F G : C ⥤ D} (a : F ⟶ G) {E : SSet.{u + 1}}
    (q : nerve D ⟶ E) :
    Arrow.mk (NerveColumn.hom (down D ≫ q) (liftedNatTrans a)) =
    Arrow.mk ((hoFunctor.map ((pre (down C)).app E)).toFunctor.map
      (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (homotopy a) q)))) := by
  change Arrow.mk ((hoFunctor.map ((ihom (nerve (ULiftHom.{u + 1} C))).map
    (down D ≫ q))).toFunctor.map (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (liftedNatTrans a))) = _
  have hb : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHom (liftedNatTrans a) =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (liftedNatTrans a))) :=
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_hom (liftedNatTrans a)).symm
  rw [hb, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp_hom, ← _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp_hom]
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomotopy_hom_arrow_of_h_eq
  change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy (liftedNatTrans a)).h ≫ (down D ≫ q) =
    (down C ▷ (Δ[1] : SSet.{u + 1})) ≫ ((homotopy a).h ≫ q)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ q) (homotopy_down_h C a)).trans (Category.assoc _ _ _))

end SerrePositivity.EInfinity.FrameHom.MixedNerve
