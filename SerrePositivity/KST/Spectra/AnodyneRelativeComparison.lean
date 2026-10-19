module

public import SerrePositivity.KST.Spectra.AnodyneHomotopyEquivalence

/-!
概要：anodyne 包含上で一致する二つの Kan 値の射の相対ホモトピー。
方針：包含上の定数ホモトピーを境界 pushout-product に沿って延長する。
規約：相対部分での射の等式を厳密に保持する。
使われ方：Goerss–Jardine I §7、VIII §1。ホーン充填から得る差の類の選択独立性。
-/

@[expose] public section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- anodyne 部分上で一致する二射は、その部分を固定してホモトピック。 -/
theorem exists_homotopy_relative_anodyne {A B Y : SSet.{u}} [KanComplex Y]
    (i : A ⟶ B) (hi : anodyneExtensions i) (f g : B ⟶ Y) (hfg : i ≫ f = i ≫ g) :
    ∃ H : SSet.Homotopy f g,
      i ▷ (Δ[1] : SSet.{u}) ≫ H.h = fst A (Δ[1] : SSet.{u}) ≫ i ≫ f := by
  let H0 : SSet.Homotopy (i ≫ f) (i ≫ g) := {
    h := fst A (Δ[1] : SSet.{u}) ≫ i ≫ f
    h₀ := by rfl
    h₁ := by rw [← hfg]; rfl
    rel := by
      ext n ⟨⟨x, hx⟩, t⟩
      exact hx.elim }
  let pp := KanRelativeLifting.boundaryProduct i
  have ha : anodyneExtensions pp.ι := SSet.anodyneExtensions_pushoutObjObjι' pp hi
  have hY : J.rlp (terminal.from Y) := (fibration_iff _).1 inferInstance
  exact KanRelativeLifting.exists_extension i (ha _ hY) f g H0

end
end SerrePositivity.KST.Spectra
