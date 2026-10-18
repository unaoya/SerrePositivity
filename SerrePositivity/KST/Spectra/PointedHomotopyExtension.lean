module

public import SerrePositivity.KST.Spectra.PointedMappingComponents
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanFibrationEndpointExtension

/-!
概要：単射な点つき部分対象上のホモトピーを全体へ延長する。
方針：区間の一端の相対充填を行い、基点の固定を部分対象の基点から回収する。
規約：標的は Kan、源は Kan でなくてもよい。
使われ方：BF 1978 §2、HTT A.3.3、Goerss–Jardine I §7。ホモトピー可換な段の比較の修正。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open SSet.modelCategoryQuillen
open SerrePositivity.SimplicialModel
open scoped Simplicial

namespace SerrePositivity.KST.Spectra.PointedExtension

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：部分対象上の基点固定ホモトピーを、指定した始点を保って全体へ延長する。
方針：単射と区間の始点の pushout-product を充填し、基点を部分対象から検査する。
規約：全体の終点の点つき射は充填の結果として得られる。
使われ方：BF 1978 §2、HTT A.3.3、Goerss–Jardine I §7。構造可換式を厳密にする相対修正。 -/
theorem exists_homotopy_from_zero {A B Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (i : A ⟶ B) [Mono i.right] (f : B ⟶ Y) (a : A ⟶ Y)
    (H : SSet.Homotopy (i.right ≫ f.right) a.right)
    (hbase : A.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
      toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom) :
    ∃ g : B ⟶ Y, i ≫ g = a ∧ ∃ V : SSet.Homotopy f.right g.right,
      B.hom ▷ (Δ[1] : SSet.{u}) ≫ V.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ Y.hom ∧
      i.right ▷ (Δ[1] : SSet.{u}) ≫ V.h = H.h := by
  have hY : J.rlp (terminal.from Y.right) := (fibration_iff _).1 inferInstance
  obtain ⟨g, hg, V, hV, _⟩ := KanFibrationEndpointExtension.exists_from_zero
    (terminal.from Y.right) hY i.right f.right a.right H (terminal.from _)
      (Subsingleton.elim _ _) (Subsingleton.elim _ _)
  have hgb : B.hom ≫ g = Y.hom := by
    rw [← Under.w i, Category.assoc, hg, Under.w a]
  let gp : B ⟶ Y := Under.homMk g hgb
  refine ⟨gp, Under.UnderMorphism.ext hg, V, ?_, hV⟩
  change B.hom ▷ (Δ[1] : SSet.{u}) ≫ V.h = _
  rw [← Under.w i, comp_whiskerRight_assoc, hV, hbase]

/-- 概要：部分対象への制限がホモトピックなら、一方の射をホモトピーで修正して制限を一致させる。
方針：写像空間の成分の等式を基点固定ホモトピーへ戻して延長する。
規約：比較するのは部分対象上の射の成分。
使われ方：Goerss–Jardine I §7、BF 1978 §2。ホモトピー可換から厳密可換への修正。 -/
theorem exists_adjustment {A B Y : PointedSimplicialSet.{u}} [KanComplex Y.right]
    (i : A ⟶ B) [Mono i.right] (f : B ⟶ Y) (a : A ⟶ Y)
    (h : π₀.mk (PointedMapping.familyVertex (i ≫ f)) =
      π₀.mk (PointedMapping.familyVertex a)) :
    ∃ g : B ⟶ Y, i ≫ g = a ∧
      π₀.mk (PointedMapping.familyVertex f) = π₀.mk (PointedMapping.familyVertex g) := by
  obtain ⟨H, hH⟩ := (PointedMapping.piZero_eq_iff_pointedHomotopy (i ≫ f) a).mp h
  obtain ⟨g, hg, V, hV, _⟩ := exists_homotopy_from_zero i f a H hH
  exact ⟨g, hg, (PointedMapping.piZero_eq_iff_pointedHomotopy f g).mpr ⟨V, hV⟩⟩

end

end SerrePositivity.KST.Spectra.PointedExtension
