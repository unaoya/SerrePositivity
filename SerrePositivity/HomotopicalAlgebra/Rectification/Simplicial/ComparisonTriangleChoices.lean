module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleHorn
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.LocalizedRelativeChoice
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RestrictionDescentEvaluation

/-!
# 中断した任意モデル源への一般化：ComparisonTriangleChoices

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The small space of all comparison triangles with both chosen edges fixed。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0367][inventory]を参照する。

[inventory]: ../../../../formalization-plans/k-theory-generalization-inventory.md#m0367
[plan]: ../../../../formalization-plans/k-theory.md
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The small space of all comparison triangles with both chosen edges fixed

Its boundary lifting preserves any earlier parameterized triangles. No
model structure is used, and the entire space is in the original universe.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ComparisonTriangleChoices
open KanComparisonTriangle
variable {T K : SSet.{v}} {f g z : T ⟶ K}
  (F : SSet.Homotopy f z) (G : SSet.Homotopy g z)

abbrev obj : SSet.{v} := RelativeChoiceSpace.obj (SSet.horn 2 2).ι (hornMap F G)

lemma horn_localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map (SSet.horn.{v} 2 2).ι) :=
  Localization.inverts AnodyneHomotopy.anodyneQ SSet.anodyneExtensions _
    (SSet.anodyneExtensions.horn_ι (2 : Fin 3))

def ofData (d : Data F G) : SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ obj F G :=
  RelativeChoiceSpace.ofExtension _ _ d.triangle (Data.horn_restriction F G d)

variable (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

include hK in
lemma terminal_mono_rlp : (MorphismProperty.monomorphisms SSet.{v}).rlp
    (terminal.from (obj F G)) :=
  LocalizedRelativeChoice.terminal_mono_rlp _ horn_localized_isIso
    (SimplexParameterHom.native_kan T K hK) _

include hK in
lemma boundary_rlp : SSet.modelCategoryQuillen.I.rlp (terminal.from (obj F G)) := by
  rw [← SSet.rlp_monomorphisms]
  exact terminal_mono_rlp F G hK

include hK in
lemma kan : SSet.modelCategoryQuillen.J.rlp (terminal.from (obj F G)) := by
  intro A B i hi
  exact terminal_mono_rlp F G hK i (SSet.modelCategoryQuillen.J_le_monomorphisms i hi)

abbrev family {L : SSet.{v}} (c : L ⟶ obj F G) :
    SSet.stdSimplex.obj (SimplexCategory.mk 2) ⊗ L ⟶ (ihom T).obj K :=
  RelativeChoiceSpace.family _ _ c

lemma family_naturality {L M : SSet.{v}} (c : L ⟶ obj F G) (i : M ⟶ L) :
    family F G (i ≫ c) = SSet.stdSimplex.obj (SimplexCategory.mk 2) ◁ i ≫ family F G c :=
  RelativeChoiceSpace.family_naturality _ _ _ _

private lemma family_face {V D Q A L : SSet.{v}} (i : V ⟶ D) (b : V ⟶ Q)
    (c : L ⟶ RelativeChoiceSpace.obj i b) (e : A ⟶ V) :
    (e ≫ i) ▷ L ≫ RelativeChoiceSpace.family i b c = fst A L ≫ (e ≫ b) := by
  rw [comp_whiskerRight, Category.assoc, RelativeChoiceSpace.family_boundary,
    ← uncurry_pre_app]
  have he : (c ≫ RelativeChoiceSpace.projection i b ≫ RelativeChoiceSpace.name b) ≫
      (pre e).app Q = (c ≫ RelativeChoiceSpace.projection i b) ≫
        RelativeChoiceSpace.name (e ≫ b) := by
    calc
      _ = (c ≫ RelativeChoiceSpace.projection i b) ≫
          (RelativeChoiceSpace.name b ≫ (pre e).app Q) := by simp only [Category.assoc]
      _ = _ := congrArg (fun k => (c ≫ RelativeChoiceSpace.projection i b) ≫ k)
        (RelativeChoiceSpace.name_precomp e b)
  rw [he]
  exact RestrictionDescentChoices.constant_name_family _ _

lemma family_zero {L : SSet.{v}} (c : L ⟶ obj F G) :
    SSet.stdSimplex.δ (0 : Fin 3) ▷ L ≫ family F G c =
      fst (SSet.stdSimplex.obj (SimplexCategory.mk 1)) L ≫ curry G.h := by
  rw [← SSet.horn.ι_ι (2 : Fin 3) 0 (by decide)]
  exact (family_face _ _ c (SSet.horn.ι 2 0 (by decide))).trans
    (congrArg (fun h => fst _ L ≫ h) (hornMap_zero F G))

lemma family_one {L : SSet.{v}} (c : L ⟶ obj F G) :
    SSet.stdSimplex.δ (1 : Fin 3) ▷ L ≫ family F G c =
      fst (SSet.stdSimplex.obj (SimplexCategory.mk 1)) L ≫ curry F.h := by
  rw [← SSet.horn.ι_ι (2 : Fin 3) 1 (by decide)]
  exact (family_face _ _ c (SSet.horn.ι 2 1 (by decide))).trans
    (congrArg (fun h => fst _ L ≫ h) (hornMap_one F G))

lemma ofData_family (d : Data F G) : family F G (ofData F G d) =
    SSet.stdSimplex.obj (SimplexCategory.mk 2) ◁ RelativeChoiceSpace.pointUnitIso.hom ≫
      (ρ_ (SSet.stdSimplex.obj (SimplexCategory.mk 2))).hom ≫ d.triangle :=
  RelativeChoiceSpace.family_ofExtension _ _ _ _

include hK in
lemma relative_extension {U V : SSet.{v}} (i : U ⟶ V) [Mono i] (c : U ⟶ obj F G) :
    ∃ e : V ⟶ obj F G, i ≫ e = c ∧
      SSet.stdSimplex.obj (SimplexCategory.mk 2) ◁ i ≫ family F G e = family F G c := by
  obtain ⟨e, he⟩ := LocalizedRelativeChoice.parameter_extension _ horn_localized_isIso
    (SimplexParameterHom.native_kan T K hK) (hornMap F G) i c
  exact ⟨e, he, by rw [← family_naturality, he]⟩

include hK in
def fixedBoundaryComparison (a b : Data F G) : RelativeChoiceSpace.FixedBoundaryHomotopy
    (SSet.horn 2 2).ι (hornMap F G) a.triangle b.triangle :=
  Classical.choice (LocalizedRelativeChoice.nonempty_fixedBoundaryHomotopy _ horn_localized_isIso
    (SimplexParameterHom.native_kan T K hK) (hornMap F G) a.triangle b.triangle
    (Data.horn_restriction F G a) (Data.horn_restriction F G b))

end SerrePositivity.SimplicialModel.ComparisonTriangleChoices
