module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationMixedTransport
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.LargeParameterSquare

/-!
# 中断した任意モデル源への一般化：AllFactorizationMixed

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One mixed square over all factorization chains。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0050][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0050
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One mixed square over all factorization chains

The four edges are the previously selected global pre/post homotopies,
transported by actual maps. Two triangles retain all four and share one
diagonal. No independent selection on each finite chain is used.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixed
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X' X Y V W : ResolutionObject C} (a : X' ⟶ X) (f : X.base ⟶ Y.base)
  (g : Y ⟶ V) (b : V ⟶ W) (φ : ResolutionLiftPrecomposition.FrameMap a)

abbrev choiceSpace := AllFactorizationPre.choiceSpace a f (g ≫ b) φ
abbrev chainMap := AnchoredChain.mapFunctor (ArrowFactorization.postTo g b (g ≫ b) rfl)
abbrev valueMap := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map (AllFactorizationMixedTransport.choiceMap hcof a f g b φ)

abbrev vertexA := chainMap g b ≫ AllFactorizationPre.direct hcof hfib a f (g ≫ b) φ
abbrev vertexB := AllFactorizationPre.direct hcof hfib a f g φ ≫ valueMap hcof a f g b φ
abbrev vertexC := chainMap g b ≫ AllFactorizationPre.transported hcof hfib a f (g ≫ b) φ
abbrev vertexD := AllFactorizationPre.transported hcof hfib a f g φ ≫ valueMap hcof a f g b φ

lemma direct_tail : AllFactorizationPost.transported hcof hfib (a.base ≫ f) g b ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map (CoherentLiftMixedComparison.mapBD hcof X' X Y W a f (g ≫ b) φ) =
      vertexB hcof hfib a f g b φ := by
  have h := congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} q)
    (AllFactorizationMixedTransport.mapBD_tail hcof a f g b φ)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_comp] at h
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => AllFactorizationComparison.chainComparison hcof hfib (a.base ≫ f) g ≫ q)
      h.symm).trans (Category.assoc _ _ _).symm)

lemma transported_tail : AllFactorizationPost.transported hcof hfib f g b ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map (CoherentLiftMixedComparison.mapAC X' X Y W a f (g ≫ b) φ) =
      vertexD hcof hfib a f g b φ := by
  have h := congrArg (fun q => _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{u} q)
    (AllFactorizationMixedTransport.mapAC_tail hcof a f g b φ)
  simp only [_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map_comp] at h
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun q => AllFactorizationComparison.chainComparison hcof hfib f g ≫ q)
      h.symm).trans (Category.assoc _ _ _).symm)

def edgeAB : SSet.Homotopy (vertexA hcof hfib a f g b φ) (vertexB hcof hfib a f g b φ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.transport (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map
      (CoherentLiftMixedComparison.mapBD hcof X' X Y W a f (g ≫ b) φ))
      (AllFactorizationPost.homotopy hcof hfib (a.base ≫ f) g b))
    (by simp only [Category.id_comp]; exact Category.assoc _ _ _)
    (by simpa only [Category.id_comp] using direct_tail hcof hfib a f g b φ)

def edgeAC : SSet.Homotopy (vertexA hcof hfib a f g b φ) (vertexC hcof hfib a f g b φ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.transport (chainMap g b) (𝟙 _)
      (AllFactorizationPre.homotopy hcof hfib a f (g ≫ b) φ))
    (by simp only [Category.comp_id]) (by simp only [Category.comp_id])

def edgeBD : SSet.Homotopy (vertexB hcof hfib a f g b φ) (vertexD hcof hfib a f g b φ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.transport (𝟙 _) (valueMap hcof a f g b φ)
      (AllFactorizationPre.homotopy hcof hfib a f g φ))
    (by simp only [Category.id_comp]) (by simp only [Category.id_comp])

def edgeCD : SSet.Homotopy (vertexC hcof hfib a f g b φ) (vertexD hcof hfib a f g b φ) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.transport (𝟙 _) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map
      (CoherentLiftMixedComparison.mapAC X' X Y W a f (g ≫ b) φ))
      (AllFactorizationPost.homotopy hcof hfib f g b))
    (by simp only [Category.id_comp]; exact Category.assoc _ _ _)
    (by simpa only [Category.id_comp] using transported_tail hcof hfib a f g b φ)

abbrev triangle (left : Bool) :=
  LargeParameterSquare.triangle (AllFactorizationPre.fillers hcof hfib a f (g ≫ b) φ)
    (edgeAB hcof hfib a f g b φ) (edgeBD hcof hfib a f g b φ)
    (edgeAC hcof hfib a f g b φ) (edgeCD hcof hfib a f g b φ) left

/-- The first retained edge is exactly the previously chosen new-source post homotopy. -/
lemma triangle_AB : AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    triangle hcof hfib a f g b φ true =
      (AllFactorizationPost.homotopy hcof hfib (a.base ≫ f) g b).h ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map
        (CoherentLiftMixedComparison.mapBD hcof X' X Y W a f (g ≫ b) φ) := by
  rw [triangle, LargeParameterSquare.left_first]
  simp only [edgeAB, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.transport,
    id_whiskerRight, Category.id_comp]

lemma triangle_BD : AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    triangle hcof hfib a f g b φ true =
      (AllFactorizationPre.homotopy hcof hfib a f g φ).h ≫ valueMap hcof a f g b φ := by
  rw [triangle, LargeParameterSquare.left_second]
  simp only [edgeBD, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.transport,
    id_whiskerRight, Category.id_comp]

lemma triangle_AC : AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫
    triangle hcof hfib a f g b φ false =
      chainMap g b ▷ SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1) ≫
        (AllFactorizationPre.homotopy hcof hfib a f (g ≫ b) φ).h := by
  rw [triangle, LargeParameterSquare.right_first]
  simp only [edgeAC, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.transport,
    Category.comp_id]

lemma triangle_CD : AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫
    triangle hcof hfib a f g b φ false =
      (AllFactorizationPost.homotopy hcof hfib f g b).h ≫ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map
        (CoherentLiftMixedComparison.mapAC X' X Y W a f (g ≫ b) φ) := by
  rw [triangle, LargeParameterSquare.right_second]
  simp only [edgeCD, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.changeEndpoints_h, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.transport,
    id_whiskerRight, Category.id_comp]

lemma common_diagonal :
    AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
        triangle hcof hfib a f g b φ true =
      AnchoredChain.simplicial g ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫
        triangle hcof hfib a f g b φ false :=
  LargeParameterSquare.common_diagonal _ _ _ _ _

/-- The values on finite chain and triangle simplices are in the original Hom universe. -/
def simplex (left : Bool) {n : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ choiceSpace a f g b φ :=
  SSet.yonedaEquiv.symm
    (((triangle hcof hfib a f g b φ left).app (Opposite.op (SimplexCategory.mk n)) (c, t)).down)

lemma simplex_naturality (left : Bool) {n m : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)).obj
      (Opposite.op (SimplexCategory.mk n)))
    (θ : SimplexCategory.mk m ⟶ SimplexCategory.mk n) :
    SSet.stdSimplex.map θ ≫ simplex hcof hfib a f g b φ left c t =
      simplex hcof hfib a f g b φ left (c.reindex θ.toOrderHom)
        ((SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)).map θ.op t) := by
  apply SSet.yonedaEquiv.injective
  rw [← SSet.yonedaEquiv_naturality]
  simp only [simplex, Equiv.apply_symm_apply]
  exact (congrArg ULift.down (congrArg (fun q => q (c, t))
    ((triangle hcof hfib a f g b φ left).naturality θ.op))).symm

lemma simplex_fixed_boundary (left : Bool) {n : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 2)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    CoherentLiftRelative.vertexInclusion X Y f ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ≫
      RelativeChoiceSpace.family (CoherentLiftRelative.vertexInclusion X Y f)
        (CoherentLiftMixedComparison.boundary X' X Y W a f (g ≫ b) φ)
        (simplex hcof hfib a f g b φ left c t) =
      CoherentLiftRelative.vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫
          CoherentLiftMixedComparison.boundary X' X Y W a f (g ≫ b) φ :=
  RelativeChoiceSpace.family_fixed_boundary _ _ _

end SerrePositivity.HomotopyFunctionComplex.AllFactorizationMixed
