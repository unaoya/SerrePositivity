module
public import SerrePositivity.KST.SConstruction.RelativeFamilyRectification

/-! # 境界固定ホモトピーの有限列と相対的な持ち上げ
概要：適合ホモトピーと逐次補正を有限列として保持し、境界を固定して持ち上げる。
方針：各区間をそのまま保存し、Kan fibration に沿う相対区間持ち上げを反復する。
規約：区間の合成代表を選び直さない。パラメータの境界は全区間で固定する。
使われ方：族の列の厳密化で、前段の補正を次段の適合条件へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SerrePositivity.InfinityCategories
open SSet.modelCategoryQuillen
open scoped Simplicial

/-- パラメータ境界を固定する、指定した実ホモトピーの有限列。 -/
inductive RelativeFamilyChain {T U E : SSet.{u}} (j : T ⟶ U) :
    (U ⟶ E) → (U ⟶ E) → Type u
  | nil (f : U ⟶ E) : RelativeFamilyChain j f f
  | cons {f g h : U ⟶ E} (H : SSet.Homotopy f g)
      (hrel : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h =
        fst T (Δ[1] : SSet.{u}) ≫ j ≫ f)
      (tail : RelativeFamilyChain j g h) : RelativeFamilyChain j f h

/-- 一区間だけの、元の指定ホモトピーを保持する有限列。 -/
def relativeFamilyChainSingle {T U E : SSet.{u}} (j : T ⟶ U) {f g : U ⟶ E}
    (H : SSet.Homotopy f g)
    (hrel : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst T (Δ[1] : SSet.{u}) ≫ j ≫ f) : RelativeFamilyChain j f g :=
  .cons H hrel (.nil g)

/-- 境界固定の有限列は元の全区間を保って連結できる。 -/
def relativeFamilyChainAppend {T U E : SSet.{u}} {j : T ⟶ U} {f g h : U ⟶ E}
    (c : RelativeFamilyChain j f g) (d : RelativeFamilyChain j g h) :
    RelativeFamilyChain j f h := by
  induction c with
  | nil => exact d
  | cons H hr tail ih => exact .cons H hr (ih d)

/-- 通常の後合成は、元の全区間と境界固定条件を保持する。 -/
def relativeFamilyChainMap {T U E B : SSet.{u}} {j : T ⟶ U} {f g : U ⟶ E}
    (c : RelativeFamilyChain j f g) (q : E ⟶ B) :
    RelativeFamilyChain j (f ≫ q) (g ≫ q) := by
  induction c with
  | nil => exact .nil _
  | cons H hr tail ih =>
    refine .cons (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp H q) ?_ ih
    simpa only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp, Category.assoc] using congrArg (· ≫ q) hr

/-- 境界固定の有限列の両端は、元の指定境界へ厳密に一致する。 -/
lemma relativeFamilyChain_boundary {T U E : SSet.{u}} {j : T ⟶ U} {f g : U ⟶ E}
    (c : RelativeFamilyChain j f g) : j ≫ g = j ≫ f := by
  induction c with
  | nil => rfl
  | @cons f g h H hr tail ih =>
    apply ih.trans
    calc
      j ≫ g = j ≫ (SSet.ι₁ ≫ H.h) := by rw [H.h₁]
      _ = SSet.ι₁ ≫ (j ▷ (Δ[1] : SSet.{u})) ≫ H.h := by rw [SSet.ι₁_comp_assoc]
      _ = SSet.ι₁ ≫ fst T (Δ[1] : SSet.{u}) ≫ j ≫ f := by rw [hr]
      _ = j ≫ f := by simp

/-- 境界固定の有限列に含まれる、元の各区間の実際の射の列。 -/
def relativeFamilyChainTrace {T U E : SSet.{u}} {j : T ⟶ U} {f g : U ⟶ E}
    (c : RelativeFamilyChain j f g) : List (U ⊗ (Δ[1] : SSet.{u}) ⟶ E) :=
  match c with
  | .nil _ => []
  | .cons H _ tail => H.h :: relativeFamilyChainTrace tail

/-- 全区間の実際の射影を元の指定区間そのものに保つ、境界固定の有限列の持ち上げ。 -/
lemma exists_relativeFamilyChain_lift_with_trace {T U E B : SSet.{u}}
    (p : E ⟶ B) [Fibration p] (j : T ⟶ U) [Mono j]
    {b a : U ⟶ B} (c : RelativeFamilyChain j b a) (f : U ⟶ E) (hf : f ≫ p = b) :
    ∃ g : U ⟶ E, g ≫ p = a ∧ ∃ d : RelativeFamilyChain j f g,
      (relativeFamilyChainTrace d).map (· ≫ p) = relativeFamilyChainTrace c := by
  induction c generalizing f with
  | nil b => exact ⟨f, hf, .nil f, rfl⟩
  | @cons b a d H hr tail ih =>
    cases hf
    obtain ⟨g, hg, _, V, hV, hbase⟩ := exists_relative_fibration_family_transport p j f H hr
    obtain ⟨k, hk, c', hc'⟩ := ih g hg
    refine ⟨k, hk, .cons V hV c', ?_⟩
    simp only [relativeFamilyChainTrace, List.map_cons]
    rw [hbase, hc']

/-- 元の指定された全区間を、境界を固定して Kan fibration に沿って持ち上げられる。 -/
lemma exists_relativeFamilyChain_lift {T U E B : SSet.{u}} (p : E ⟶ B) [Fibration p]
    (j : T ⟶ U) [Mono j] {b a : U ⟶ B} (c : RelativeFamilyChain j b a)
    (f : U ⟶ E) (hf : f ≫ p = b) :
    ∃ g : U ⟶ E, g ≫ p = a ∧ Nonempty (RelativeFamilyChain j f g) := by
  obtain ⟨g, hg, d, _⟩ := exists_relativeFamilyChain_lift_with_trace p j c f hf
  exact ⟨g, hg, ⟨d⟩⟩

end SerrePositivity.KST.SConstruction
