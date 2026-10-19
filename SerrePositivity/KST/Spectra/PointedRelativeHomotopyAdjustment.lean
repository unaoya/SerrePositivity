module

public import SerrePositivity.KST.Spectra.PointedHomotopyExtension

/-!
概要：指定した標的への合成を固定したまま、部分対象上の点つきホモトピーを延長する。
方針：Kan fibration の始点延長を使い、元の部分対象の基点から全体の基点固定を回収する。
規約：源の Kan 性は不要。使われ方：指定パラメータ部分を保つ列の相対厳密化。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open scoped Simplicial
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Spectra.PointedExtension

/-- 標的への合成を全区間で固定し、元の基点と部分対象上のホモトピーを保って延長する。 -/
lemma exists_homotopy_from_zero_over {A T E B : PointedSimplicialSet.{u}}
    (p : E ⟶ B) (hp : SSet.modelCategoryQuillen.J.rlp p.right)
    (i : A ⟶ T) [Mono i.right]
    (f : T ⟶ E) (a : A ⟶ E) (b : T ⟶ B) (hf : f ≫ p = b)
    (H : SSet.Homotopy (i.right ≫ f.right) a.right)
    (hbase : A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E.hom)
    (hvertical : H.h ≫ p.right = fst A.right (Δ[1] : SSet.{u}) ≫ i.right ≫ b.right) :
    ∃ g : T ⟶ E, i ≫ g = a ∧ g ≫ p = b ∧
      ∃ V : SSet.Homotopy f.right g.right,
        T.hom ▷ (Δ[1] : SSet.{u}) ≫ V.h =
          toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ E.hom ∧
        i.right ▷ (Δ[1] : SSet.{u}) ≫ V.h = H.h ∧
        V.h ≫ p.right = fst T.right (Δ[1] : SSet.{u}) ≫ b.right := by
  let q := fst T.right (Δ[1] : SSet.{u}) ≫ b.right
  have h0 : f.right ≫ p.right = SSet.ι₀ ≫ q := by
    have he := congrArg Under.Hom.right hf
    change f.right ≫ p.right = b.right at he
    rw [he]
    rfl
  have hi : H.h ≫ p.right = i.right ▷ (Δ[1] : SSet.{u}) ≫ q := by
    rw [hvertical]
    exact (whiskerRight_fst_assoc i.right (Δ[1] : SSet.{u}) b.right).symm
  obtain ⟨g, hg, V, hV, hP⟩ := KanFibrationEndpointExtension.exists_from_zero
    p.right hp i.right f.right a.right H q h0 hi
  have hgb : T.hom ≫ g = E.hom := by
    rw [← Under.w i, Category.assoc, hg, Under.w a]
  let gp : T ⟶ E := Under.homMk g hgb
  refine ⟨gp, Under.UnderMorphism.ext hg, ?_, V, ?_, hV, hP⟩
  · apply Under.UnderMorphism.ext
    have he := congrArg (SSet.ι₁ ≫ ·) hP
    rw [← Category.assoc, V.h₁] at he
    exact he
  · rw [← Under.w i, comp_whiskerRight_assoc, hV, hbase]

end SerrePositivity.KST.Spectra.PointedExtension
