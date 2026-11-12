module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.RelativeDiagramHomotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.HornColimits

/-!
概要：同じ前辺・後辺を持つ合成三角形を相対的に比較する。
方針：二辺の pushout でホーンへの制限を照合し、inner anodyne 制限の fiber を使う。
規約：対角辺の一致は仮定しない。二辺を固定する実際のホモトピーを得る。
使われ方：B1 の comma 正方形と基準合成三角形の coherence の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：二辺を共有する合成三角形は内ホーン上で厳密に一致する。
方針：ホーンの pushout の二つの辺で確認する。
規約：対角辺は異なってよい。
使われ方：二辺を固定した相対ホモトピーの入力。 -/
lemma FunctorCompositionTriangle.horn_eq {A X : SSet.{u}} {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (T₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₁) :
    (horn 2 1).ι ≫ T₀.diagram = (horn 2 1).ι ≫ T₁.diagram := by
  apply horn₂₁.isPushout.hom_ext
  · simpa only [← Category.assoc, horn.ι_ι] using T₀.face_two.trans T₁.face_two.symm
  · simpa only [← Category.assoc, horn.ι_ι] using T₀.face_zero.trans T₁.face_zero.symm

/-- 概要：同じ二辺を持つ合成三角形の相対ホモトピーを選ぶ。
方針：内ホーンの包含が inner anodyne であることを使う。
規約：二辺上では時間方向に定値で、始点・終点は指定三角形そのもの。
使われ方：標準単位比較における合成の選択と元の正方形を比較する。 -/
noncomputable def FunctorCompositionTriangle.relativeHomotopy
    {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (T₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₁) : SSet.Homotopy T₀.diagram T₁.diagram :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.exists_homotopy_relative_innerAnodyne (horn 2 1).ι
    (innerAnodyneExtensions.horn_ι (by decide) (by decide))
    T₀.diagram T₁.diagram (T₁.horn_eq T₀)).choose

/-- 概要：三角形の比較ホモトピーのホーン制限は一定。
方針：相対ホモトピーの選択の仕様を取り出す。
規約：ホモトピーの raw な射の等式。
使われ方：二辺とその頂点を固定した対角辺の比較。 -/
lemma FunctorCompositionTriangle.relativeHomotopy_horn
    {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (T₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₁) :
    ((horn 2 1).ι ▷ (Δ[1] : SSet.{u})) ≫ (T₀.relativeHomotopy T₁).h =
      fst _ (Δ[1] : SSet.{u}) ≫ (horn 2 1).ι ≫ T₀.diagram :=
  (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.exists_homotopy_relative_innerAnodyne (horn 2 1).ι
    (innerAnodyneExtensions.horn_ι (by decide) (by decide))
    T₀.diagram T₁.diagram (T₁.horn_eq T₀)).choose_spec

/-- 概要：比較中も前辺・後辺は元の射そのものに定値。
方針：ホーンの制限の等式を各面の包含で前合成する。
規約：i は対角辺以外の面。
使われ方：対角辺を動かす正方形の端点固定条件。 -/
lemma FunctorCompositionTriangle.relativeHomotopy_face
    {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (T₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₁) (i : Fin 3) (hi : i ≠ 1) :
    (stdSimplex.δ i ▷ (Δ[1] : SSet.{u})) ≫ (T₀.relativeHomotopy T₁).h =
      fst _ (Δ[1] : SSet.{u}) ≫ stdSimplex.δ i ≫ T₀.diagram := by
  have h := congrArg (fun f ↦ (horn.ι 1 i hi ▷ (Δ[1] : SSet.{u})) ≫ f)
    (T₀.relativeHomotopy_horn T₁)
  simp only [← Category.assoc] at h
  rw [← MonoidalCategory.comp_whiskerRight, horn.ι_ι, whiskerRight_fst] at h
  simpa only [Category.assoc, reassoc_of% horn.ι_ι] using h

/-- 概要：二辺を固定した三角形の比較を対角辺の正方形へ制限する。
方針：比較の raw なホモトピーを第 1 面で前合成する。
規約：二つの横辺は指定された対角辺の代表。
使われ方：元の合成三角形の情報を保持した写像空間比較の path。 -/
noncomputable def FunctorCompositionTriangle.diagonalHomotopy
    {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (T₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₁) : SSet.Homotopy (curry d₀.h) (curry d₁.h) where
  h := (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) ≫ (T₀.relativeHomotopy T₁).h
  h₀ := by
    have hn : (SSet.ι₀ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) =
        stdSimplex.δ (1 : Fin 3) ≫ SSet.ι₀ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hn, Category.assoc, SSet.Homotopy.h₀, T₀.face_one]
    rfl
  h₁ := by
    have hn : (SSet.ι₁ : (Δ[1] : SSet.{u}) ⟶ Δ[1] ⊗ Δ[1]) ≫
        (stdSimplex.δ (1 : Fin 3) ▷ (Δ[1] : SSet.{u})) =
        stdSimplex.δ (1 : Fin 3) ≫ SSet.ι₁ := by
      apply SSet.hom_ext
      intro n
      apply ConcreteCategory.hom_ext
      intro x
      rfl
    rw [← Category.assoc, hn, Category.assoc, SSet.Homotopy.h₁, T₁.face_one]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property

/-- 概要：対角辺の比較は始点の関手を固定する。
方針：始点を共有する前辺の定値性へ帰着する。
規約：頂点の一致だけでなく時間方向の射の等式。
使われ方：端点固定の区間写像空間への持ち上げ。 -/
lemma FunctorCompositionTriangle.diagonalHomotopy_source
    {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (T₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₁) :
    (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ (T₀.diagonalHomotopy T₁).h =
      fst _ (Δ[1] : SSet.{u}) ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex U) := by
  have hv : (stdSimplex.δ (1 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (1 : Fin 3) = stdSimplex.δ (1 : Fin 2) ≫ stdSimplex.δ (2 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  change (_ ▷ _) ≫ ((_ ▷ _) ≫ (T₀.relativeHomotopy T₁).h) = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, hv,
    MonoidalCategory.comp_whiskerRight, Category.assoc,
    T₀.relativeHomotopy_face T₁ 2 (by decide), ← Category.assoc,
    whiskerRight_fst, Category.assoc, T₀.vertex_zero]

/-- 概要：対角辺の比較は終点の関手を固定する。
方針：終点を共有する後辺の定値性へ帰着する。
規約：頂点の一致だけでなく時間方向の射の等式。
使われ方：端点固定の区間写像空間への持ち上げ。 -/
lemma FunctorCompositionTriangle.diagonalHomotopy_target
    {A X : SSet.{u}} [Quasicategory X] {U V W : A ⟶ X}
    {l : SSet.Homotopy U V} {r : SSet.Homotopy V W}
    {d₀ d₁ : SSet.Homotopy U W} (T₀ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₀)
    (T₁ : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorCompositionTriangle l r d₁) :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ (T₀.diagonalHomotopy T₁).h =
      fst _ (Δ[1] : SSet.{u}) ≫ SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex W) := by
  have hv : (stdSimplex.δ (0 : Fin 2) : (Δ[0] : SSet.{u}) ⟶ Δ[1]) ≫
      stdSimplex.δ (1 : Fin 3) = stdSimplex.δ (0 : Fin 2) ≫ stdSimplex.δ (0 : Fin 3) := by
    apply SSet.yonedaEquiv.injective
    decide
  change (_ ▷ _) ≫ ((_ ▷ _) ≫ (T₀.relativeHomotopy T₁).h) = _
  rw [← Category.assoc, ← MonoidalCategory.comp_whiskerRight, hv,
    MonoidalCategory.comp_whiskerRight, Category.assoc,
    T₀.relativeHomotopy_face T₁ 0 (by decide), ← Category.assoc,
    whiskerRight_fst, Category.assoc, T₀.vertex_two]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
