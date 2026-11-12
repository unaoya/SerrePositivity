module
public import SerrePositivity.KST.SConstruction.FixedBoundaryPostcomposition

/-! # 元の全境界固定円柱をパラメータ制限で保持
概要：元の境界四角形に沿って円柱を制限し、全比較時刻の境界固定式を保持する。
方針：元の可換四角形と tensor の自然性で、同じ実円柱の全制限を回収する。
規約：円柱を選び直さず、全パラメータ・全時刻での実写像の等号を使う。
使われ方：累積補正の全二次元比較を、元の直通列点の実辺へ制限する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 元の境界四角形に沿う全円柱の制限は、同じ全境界固定式を保持する。 -/
lemma fixedBoundaryHomotopy_pullback {A T A' T' E : SSet.{u}}
    (j : A ⟶ T) (j' : A' ⟶ T') (p : T' ⟶ T) (k : A' ⟶ A)
    (hp : j' ≫ p = k ≫ j) {f g : T ⟶ E} (H : SSet.Homotopy f g) (b : A ⟶ E)
    (hr : (j ▷ (Δ[1] : SSet.{u})) ≫ H.h = fst A Δ[1] ≫ b) :
    (j' ▷ (Δ[1] : SSet.{u})) ≫ (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H p).h =
      fst A' Δ[1] ≫ k ≫ b := by
  change _ ≫ (p ▷ (Δ[1] : SSet.{u})) ≫ H.h = _
  rw [← comp_whiskerRight_assoc, hp, comp_whiskerRight, Category.assoc, hr,
    whiskerRight_fst_assoc]

/-- 元の指定頂点を固定し、元の全区間だけを動かす実パラメータ。 -/
def intervalParameterPoint {P : SSet.{u}} (v : P _⦋0⦌) : (Δ[1] : SSet.{u}) ⟶ P ⊗ Δ[1] :=
  lift (SSet.const v) (𝟙 _)

/-- 同じ指定頂点を固定した、元の区間境界全体の実パラメータ。 -/
def intervalParameterBoundaryPoint {P : SSet.{u}} (v : P _⦋0⦌) :
    (∂Δ[1] : SSet.{u}) ⟶ P ⊗ (∂Δ[1] : SSet.{u}) :=
  lift (SSet.const v) (𝟙 _)

/-- 元の区間境界と一点制限の全四角形は厳密に可換。 -/
lemma intervalParameterPoint_boundary {P : SSet.{u}} (v : P _⦋0⦌) :
    (SSet.boundary 1).ι ≫ intervalParameterPoint v =
      intervalParameterBoundaryPoint v ≫ (P ◁ (SSet.boundary 1).ι) := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [intervalParameterPoint, intervalParameterBoundaryPoint, Category.assoc,
      lift_fst, lift_snd, whiskerLeft_fst, whiskerLeft_snd, SSet.comp_const,
      Category.comp_id, Category.id_comp, lift_snd_assoc]

/-- 元の零単体上の円柱の一点制限は、同じ指定頂点の区間パラメータそのもの。 -/
lemma intervalParameterPoint_of_map {P : SSet.{u}} (p : (Δ[0] : SSet.{u}) ⟶ P) :
    lift (SSet.const (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})))) (𝟙 (Δ[1] : SSet.{u})) ≫
        (p ▷ (Δ[1] : SSet.{u})) = intervalParameterPoint (SSet.yonedaEquiv p) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [intervalParameterPoint, Category.assoc, whiskerRight_fst, lift_fst]
    rw [← Category.assoc, lift_fst, SSet.const_comp]
    rfl
  · simp only [intervalParameterPoint, Category.assoc, whiskerRight_snd, lift_snd]

/-- 一点制限後も、全区間境界を全比較時刻で厳密に固定する。 -/
lemma fixedBoundaryHomotopy_intervalPoint {P E : SSet.{u}} (v : P _⦋0⦌)
    {f g : P ⊗ (Δ[1] : SSet.{u}) ⟶ E} (H : SSet.Homotopy f g)
    (hr : ((P ◁ (SSet.boundary 1).ι) ▷ (Δ[1] : SSet.{u})) ≫ H.h =
      fst (P ⊗ (∂Δ[1] : SSet.{u})) Δ[1] ≫ (P ◁ (SSet.boundary 1).ι) ≫ f) :
    ((SSet.boundary 1).ι ▷ (Δ[1] : SSet.{u})) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp H (intervalParameterPoint v)).h =
      fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ (SSet.boundary 1).ι ≫ intervalParameterPoint v ≫ f := by
  have h := fixedBoundaryHomotopy_pullback (P ◁ (SSet.boundary 1).ι) (SSet.boundary 1).ι
    (intervalParameterPoint v) (intervalParameterBoundaryPoint v)
    (intervalParameterPoint_boundary v) H _ hr
  have he := congrArg (fun q => fst (∂Δ[1] : SSet.{u}) Δ[1] ≫ q ≫ f)
    (intervalParameterPoint_boundary v).symm
  exact h.trans (by simpa only [Category.assoc] using he)

end SerrePositivity.KST.SConstruction
