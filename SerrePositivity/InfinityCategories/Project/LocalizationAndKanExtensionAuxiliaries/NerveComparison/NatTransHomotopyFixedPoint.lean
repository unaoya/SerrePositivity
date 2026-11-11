module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.NatTransHomotopyComponent
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinTensorPoint

/-!
概要：自然変換による錐の後合成を頂点を固定したホモトピーで表す。
方針：指数比較の成分公式と区間の Yoneda 表示を使う。
規約：図式上では元の指定変換を保持する。
使われ方：B5 の指定余単位の局所錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison


/-- 概要：頂点を標準の退化一次単体で評価すると恒等辺になる。
方針：指定自然変換の成分と join の包含を比較する。
規約：同じ宇宙の小さい圏の元の図式を保つ。
使われ方：B5 の指定局所錐の古典比較。 -/
lemma nervePoint_degenerateEdge {A : Type u} [Category.{u} A] (x : A) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint x).app (Opposite.op ⦋1⦌)
      (stdSimplex.objEquiv.symm (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)) =
        (SSet.Truncated.Edge.id (X := (truncation 2).obj (nerve A)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x)).edge := by
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
variable {C D : Type u} [Category.{u} C] [Category.{u} D] {F G : C ⥤ D}

/-- 概要：成分が恒等な点でホモトピー表示は時間に定値。
方針：指定自然変換の成分と join の包含を比較する。
規約：同じ宇宙の小さい圏の元の図式を保つ。
使われ方：B5 の指定局所錐の古典比較。 -/
lemma nerveNatTransHomotopy_fixedPoint (η : F ⟶ G) (x : C) (y : D)
    (he : (nerve.edgeMk (η.app x)).edge = (nerve.edgeMk (𝟙 y)).edge) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint x ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy η).h =
      fst (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint y := by
  let k : (Δ[1] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⊗ Δ[1] :=
    lift (stdSimplex.isTerminalObj₀.from Δ[1]) (𝟙 _)
  have hk : k = inv (snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u})) := by
    apply (cancel_mono (snd (Δ[0] : SSet.{u}) (Δ[1] : SSet.{u}))).1
    rw [IsIso.inv_hom_id]
    exact lift_snd _ _
  have : IsIso k := by rw [hk]; infer_instance
  apply (cancel_epi k).1
  let z : (Δ[1] : SSet.{u}) _⦋1⦌ := stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)
  have hka : k.app (Opposite.op ⦋1⦌) z =
      (stdSimplex.objEquiv.symm (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0), z) := by
    apply Prod.ext
    · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
        (lift_fst (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _))
          (Opposite.op ⦋1⦌)) z
      exact h
    · have h := ConcreteCategory.congr_hom (NatTrans.congr_app
        (lift_snd (stdSimplex.isTerminalObj₀.from (Δ[1] : SSet.{u})) (𝟙 _))
          (Opposite.op ⦋1⦌)) z
      exact h
  apply SSet.yonedaEquiv.injective
  change (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy η).h.app (Opposite.op ⦋1⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint x).app (Opposite.op ⦋1⦌) (k.app (Opposite.op ⦋1⦌) z).1,
      (k.app (Opposite.op ⦋1⦌) z).2) =
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint y).app (Opposite.op ⦋1⦌) (k.app (Opposite.op ⦋1⦌) z).1
  rw [hka]
  rw [nervePoint_degenerateEdge, nervePoint_degenerateEdge]
  have hz : z = _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyIntervalEdge.edge := by
    apply stdSimplex.objEquiv.injective
    apply SimplexCategory.Hom.ext
    apply DFunLike.ext
    intro i
    fin_cases i <;> rfl
  rw [hz]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy η) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x)).edge = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveNatTransHomotopy_component, he]
  change ComposableArrows.mk₁ (𝟙 y) = _
  have hi := congrArg SSet.Edge.edge (nerve.edgeMk_id y)
  exact hi

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
