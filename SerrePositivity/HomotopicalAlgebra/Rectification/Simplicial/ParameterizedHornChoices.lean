module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ParameterChoiceDiagram
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.LocalizedRelativeChoice
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RestrictionDescentEvaluation
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
# 中断した任意モデル源への一般化：ParameterizedHornChoices

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Relative choices of whole horn fillers in every dimension。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0511][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0511
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative choices of whole horn fillers in every dimension

A compatible family of specified faces is glued to the actual horn.
All fillers form one small simplicial set with extension along every
parameter monomorphism, preserving every specified whole face. The
same root family restricts naturally over the whole parameter category.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ParameterizedHornChoices
variable (T K : SSet.{v}) {n : ℕ} {i : Fin (n + 2)}
  (faces : ∀ (j : Fin (n + 2)) (_ : j ≠ i),
    SSet.stdSimplex.obj (SimplexCategory.mk n) ⟶ (ihom T).obj K)
  (hf : SSet.horn.IsCompatible faces)

abbrev obj : SSet.{v} := RelativeChoiceSpace.obj (SSet.horn (n + 1) i).ι hf.desc

lemma horn_localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (SSet.horn.{v} (n + 1) i).ι) :=
  Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
    (SSet.anodyneExtensions.horn_ι i)

lemma filler_restriction
    (a : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ (ihom T).obj K)
    (ha : ∀ j hj, SSet.stdSimplex.δ j ≫ a = faces j hj) :
    (SSet.horn (n + 1) i).ι ≫ a = hf.desc := by
  apply SSet.horn.hom_ext'
  intro j hj
  rw [← Category.assoc, SSet.horn.ι_ι]
  exact (ha j hj).trans (hf.ι_desc j hj).symm

def ofFiller (a : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ (ihom T).obj K)
    (ha : ∀ j hj, SSet.stdSimplex.δ j ≫ a = faces j hj) :
    SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ obj T K faces hf :=
  RelativeChoiceSpace.ofExtension _ _ a (filler_restriction T K faces hf a ha)

abbrev family {L : SSet.{v}} (c : L ⟶ obj T K faces hf) :
    SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⊗ L ⟶ (ihom T).obj K :=
  RelativeChoiceSpace.family _ _ c

lemma family_face {L : SSet.{v}} (c : L ⟶ obj T K faces hf) (j : Fin (n + 2)) (hj : j ≠ i) :
    SSet.stdSimplex.δ j ▷ L ≫ family T K faces hf c =
      fst (SSet.stdSimplex.obj (SimplexCategory.mk n)) L ≫ faces j hj := by
  let e := SSet.horn.ι i j hj
  rw [← SSet.horn.ι_ι i j hj, comp_whiskerRight, Category.assoc]
  change e ▷ L ≫ ((SSet.horn (n + 1) i).ι ▷ L ≫ RelativeChoiceSpace.family _ _ c) = _
  rw [RelativeChoiceSpace.family_boundary, ← uncurry_pre_app]
  have he : (c ≫ RelativeChoiceSpace.projection _ hf.desc ≫ RelativeChoiceSpace.name hf.desc) ≫
      (pre e).app ((ihom T).obj K) =
      (c ≫ RelativeChoiceSpace.projection _ hf.desc) ≫ RelativeChoiceSpace.name (e ≫ hf.desc) := by
    calc
      _ = (c ≫ RelativeChoiceSpace.projection _ hf.desc) ≫
          (RelativeChoiceSpace.name hf.desc ≫ (pre e).app ((ihom T).obj K)) := by
        simp only [Category.assoc]
      _ = _ := congrArg (fun q => (c ≫ RelativeChoiceSpace.projection _ hf.desc) ≫ q)
        (RelativeChoiceSpace.name_precomp e hf.desc)
  rw [he, RestrictionDescentChoices.constant_name_family]
  exact congrArg (fun q => fst _ L ≫ q) (hf.ι_desc j hj)

lemma ofFiller_family
    (a : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ (ihom T).obj K)
    (ha : ∀ j hj, SSet.stdSimplex.δ j ≫ a = faces j hj) :
    family T K faces hf (ofFiller T K faces hf a ha) =
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁ RelativeChoiceSpace.pointUnitIso.hom ≫
        (ρ_ (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)))).hom ≫ a :=
  RelativeChoiceSpace.family_ofExtension _ _ _ _

abbrev diagram : (Over T)ᵒᵖ ⥤ SSet.{v} :=
  ParameterChoiceDiagram.diagram T K (SSet.horn (n + 1) i).ι hf.desc

abbrev naturalFamily {L : SSet.{v}} (c : L ⟶ obj T K faces hf) :=
  ParameterChoiceDiagram.family T K (SSet.horn (n + 1) i).ι hf.desc c

abbrev naturalPoint
    (a : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ (ihom T).obj K)
    (ha : ∀ j hj, SSet.stdSimplex.δ j ≫ a = faces j hj) :=
  naturalFamily T K faces hf (ofFiller T K faces hf a ha)

lemma naturalPoint_projection
    (a : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ (ihom T).obj K)
    (ha : ∀ j hj, SSet.stdSimplex.δ j ≫ a = faces j hj) :
    naturalPoint T K faces hf a ha ≫
      ParameterChoiceDiagram.projection T K (SSet.horn (n + 1) i).ι hf.desc = 𝟙 _ :=
  ParameterChoiceDiagram.point_projection T K _ _ a (filler_restriction T K faces hf a ha)

def evaluatedAt {L : SSet.{v}} (c : L ⟶ obj T K faces hf) (σ : (Over T)ᵒᵖ) :
    σ.unop.left ⊗ (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⊗ L) ⟶ K :=
  uncurry (RelativeChoiceSpace.family (SSet.horn (n + 1) i).ι
    ((ParameterChoiceDiagram.parameterize T K hf.desc).app σ)
    ((naturalFamily T K faces hf c).app σ))

lemma evaluatedAt_restriction {L : SSet.{v}} (c : L ⟶ obj T K faces hf) (σ : (Over T)ᵒᵖ) :
    evaluatedAt T K faces hf c σ =
      σ.unop.hom ▷ (SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⊗ L) ≫
        uncurry (family T K faces hf c) := by
  rw [evaluatedAt, ParameterChoiceDiagram.family_evaluation]
  exact uncurry_pre_app K (family T K faces hf c) σ.unop.hom

variable (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include hK in
lemma terminal_mono_rlp : (MorphismProperty.monomorphisms SSet.{v}).rlp
    (terminal.from (obj T K faces hf)) :=
  LocalizedRelativeChoice.terminal_mono_rlp _ horn_localized_isIso
    (SimplexParameterHom.native_kan T K hK) _

include hK in
lemma relative_extension {U V : SSet.{v}} (j : U ⟶ V) [Mono j]
    (c : U ⟶ obj T K faces hf) :
    ∃ d : V ⟶ obj T K faces hf, j ≫ d = c ∧
      SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ◁ j ≫ family T K faces hf d =
        family T K faces hf c ∧
      (Functor.const (Over T)ᵒᵖ).map j ≫ naturalFamily T K faces hf d =
        naturalFamily T K faces hf c := by
  obtain ⟨d, hd⟩ := LocalizedRelativeChoice.parameter_extension _ horn_localized_isIso
    (SimplexParameterHom.native_kan T K hK) hf.desc j c
  refine ⟨d, hd, ?_, ?_⟩
  · rw [← RelativeChoiceSpace.family_naturality, hd]
  · apply NatTrans.ext
    funext σ
    change j ≫ (d ≫ (ParameterChoiceDiagram.transport T K _ hf.desc).app σ) = _
    rw [← Category.assoc, hd]
    rfl

include hK in
def fixedFacesComparison
    (a b : SSet.stdSimplex.obj (SimplexCategory.mk (n + 1)) ⟶ (ihom T).obj K)
    (ha : ∀ j hj, SSet.stdSimplex.δ j ≫ a = faces j hj)
    (hb : ∀ j hj, SSet.stdSimplex.δ j ≫ b = faces j hj) :
    RelativeChoiceSpace.FixedBoundaryHomotopy (SSet.horn (n + 1) i).ι hf.desc a b :=
  Classical.choice (LocalizedRelativeChoice.nonempty_fixedBoundaryHomotopy _ horn_localized_isIso
    (SimplexParameterHom.native_kan T K hK) hf.desc a b
    (filler_restriction T K faces hf a ha) (filler_restriction T K faces hf b hb))

end SerrePositivity.SimplicialModel.ParameterizedHornChoices
