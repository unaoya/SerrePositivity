module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.RelativeFunctorHomotopyComposition
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-! # 部分図式で定値なホモトピーの端点と合成

概要：全時刻の固定条件から両端点の厳密な制限を回収し、同じ条件を保って合成する。
方針：区間端点で評価し、制限の fiber 内の既存の相対合成を使う。
規約：部分図式上の射そのものを固定する。使われ方：有限係数骨格の比較の帰納。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
section
variable {L K X : SSet.{u}} (i : L ⟶ K) {f g : K ⟶ X} (a : L ⟶ X)
variable (H : SSet.Homotopy f g)
variable (hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst L Δ[1] ≫ a)

include hH

/-- 定値な部分ホモトピーの始点は指定した部分写像である。 -/
lemma fixedDiagramHomotopy_source : i ≫ f = a := by
  have h := congrArg (fun k => SSet.ι₀ ≫ k) hH
  rw [← Category.assoc, SSet.ι₀_comp, Category.assoc, H.h₀,
    ← Category.assoc, SSet.ι₀_fst, Category.id_comp] at h
  exact h

/-- 定値な部分ホモトピーの終点も指定した部分写像である。 -/
lemma fixedDiagramHomotopy_target : i ≫ g = a := by
  have h := congrArg (fun k => SSet.ι₁ ≫ k) hH
  rw [← Category.assoc, SSet.ι₁_comp, Category.assoc, H.h₁,
    ← Category.assoc, SSet.ι₁_fst, Category.id_comp] at h
  exact h

/-- 同じ部分図式を全時刻固定する二つのホモトピーを合成できる。 -/
lemma fixedDiagramHomotopyComposite_exists [Quasicategory X] [Mono i] {h : K ⟶ X}
    (R : SSet.Homotopy g h)
    (hR : (i ▷ (Δ[1] : SSet.{u})) ≫ R.h = fst L Δ[1] ≫ a) :
    ∃ T : SSet.Homotopy f h,
      (i ▷ (Δ[1] : SSet.{u})) ≫ T.h = fst L Δ[1] ≫ a := by
  obtain ⟨T, hT, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.exists_relativeFunctorHomotopyComposite i a
    (fixedDiagramHomotopy_source i a H hH) (fixedDiagramHomotopy_target i a H hH)
    (fixedDiagramHomotopy_target i a R hR) H R hH hR
  exact ⟨T, hT⟩

end

/-- 部分図式上の全時刻固定は、その任意の部分図式への制限でも保たれる。 -/
lemma fixedDiagramHomotopy_restrict {M L K X : SSet.{u}} (j : M ⟶ L) (i : L ⟶ K)
    {f g : K ⟶ X} (a : L ⟶ X) (H : SSet.Homotopy f g)
    (hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst L Δ[1] ≫ a) :
    ((j ≫ i) ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst M Δ[1] ≫ j ≫ a := by
  rw [comp_whiskerRight, Category.assoc, hH, ← Category.assoc, whiskerRight_fst,
    Category.assoc]

/-- 全時刻固定の比較を後合成しても、同じ部分図式上の固定条件を保つ。 -/
lemma fixedDiagramHomotopy_postcomp {L K X Y : SSet.{u}} (i : L ⟶ K)
    {f g : K ⟶ X} (a : L ⟶ X) (H : SSet.Homotopy f g)
    (hH : (i ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst L Δ[1] ≫ a) (q : X ⟶ Y) :
    (i ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H q).h =
      fst L Δ[1] ≫ a ≫ q := by
  change _ ≫ (H.h ≫ q) = _
  rw [← Category.assoc, hH, Category.assoc]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
