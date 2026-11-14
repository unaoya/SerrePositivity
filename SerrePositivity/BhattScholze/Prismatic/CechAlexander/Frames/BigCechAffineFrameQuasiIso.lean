module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechVertexFrame
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechVertexFrame
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.BigCechAffineEnvelope
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechAlexander
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Frames.BigCechFrameComparison
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeConstruction
import all SerrePositivity.BhattScholze.Prismatic.Site.PrismOver

/-!
## 概要
有限affine枠と標準の大きい枠とのČech–Alexander比較射の擬同型性を示す。

## 方針
両方の枠を同じ濃度上限に置き、混合頂点の余鎖ホモトピーを既存の比較射へ移す。

## 規約
有界な向き付きプリズムPと有限多項式枠Qを固定し、polyCutoffによる濃度上限を使う。

## 使われ方
Čech–Alexander比較において有限affine枠と標準の大きい枠を比較する。
-/

public noncomputable section

open CategoryTheory AlgebraicTopology Cardinal

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (hP : IsBoundedPrism P) (Q : Poly (A ⧸ P.ideal))

private theorem affineBigCechTerm_small (n : ℕ) :
    Cardinal.mk (affineBigCechTerm P Q n hP).carrier ≤ polyCutoff P Q.n := by
  change Cardinal.mk (completedFreeDelta P (BigCechIndex P Q n)) ≤ polyCutoff P Q.n
  apply (cardinal_envelope_le P _).trans
  unfold polyCutoff cutoff
  apply Cardinal.power_le_power_right
  have h : Cardinal.mk (BigCechIndex P Q n) ≤
      max (Cardinal.mk (polyCompletion P Q.n)) Cardinal.aleph0 := by
    change Cardinal.mk (polyCompletion P Q.n × Fin (n+1)) ≤ _
    rw [Cardinal.mk_prod, Cardinal.lift_uzero]
    have hf : Cardinal.lift.{u} (Cardinal.mk (Fin (n+1))) ≤ Cardinal.aleph0 :=
      (Cardinal.lift_le_aleph0).2 Cardinal.mk_le_aleph0
    calc
      _ ≤ Cardinal.mk (polyCompletion P Q.n) * Cardinal.aleph0 := by gcongr
      _ ≤ _ := Cardinal.mul_le_max_of_aleph0_le_right le_rfl
  rw [add_assoc, add_assoc]
  apply add_le_add_right
  have h₀ : Cardinal.aleph0 ≤ max (Cardinal.mk (polyCompletion P Q.n)) Cardinal.aleph0 :=
    le_max_right _ _
  calc
    Cardinal.mk (BigCechIndex P Q n) + Cardinal.aleph0 ≤
        max (Cardinal.mk (polyCompletion P Q.n)) Cardinal.aleph0 + Cardinal.aleph0 :=
      add_le_add_left h _
    _ = max (Cardinal.mk (polyCompletion P Q.n)) Cardinal.aleph0 := by
      rw [Cardinal.add_eq_max' le_rfl, max_eq_left h₀]
    _ ≤ _ := max_le (self_le_add_right _ _) (self_le_add_left _ _)

local notation "U" => fun n => affineEnvelopeTerm P hP Q.n n (polyCutoff P Q.n) le_rfl
local notation "E" => fun Q n => affineBigCechTerm P Q n hP
local notation "F" => prismSiteAlgebras P (polyCompletion P Q.n) (polyCutoff P Q.n)
local notation "B" => BigCechVertexFrame.model P Q E
  (fun n => affineBigCechTerm_bounded P Q n hP) (affineBigCechTerm_small P hP Q)
local notation "j" => BigCechVertexFrame.toBig P Q E
  (fun n => affineBigCechTerm_bounded P Q n hP) (affineBigCechTerm_small P hP Q) U

private def bigFrameAlgebraIso : B ⋙ F ≅ (bigCechAlexander P hP).obj Q :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro m n θ
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    apply Under.UnderMorphism.ext
    apply CommRingCat.hom_ext
    rfl)

private theorem comparison_whisker :
    Functor.whiskerRight j F ≫ (bigFrameAlgebraIso P hP Q).hom =
      affineCechAlexanderFrame (P := P) hP Q := by
  ext n : 1
  change (F).map ((j).app n) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  apply Under.UnderMorphism.ext
  apply CommRingCat.hom_ext
  rfl

set_option maxHeartbeats 800000 in
-- 標準模型と台の余単体的代数の型を照合する。
/-- 標準の有限枠から大きい枠への比較は交代余面複体の擬同型。 -/
theorem affineCechAlexanderFrame_quasiIso :
    QuasiIso ((alternatingCofaceMapComplex _).map
      (Functor.whiskerRight (affineCechAlexanderFrame (P := P) hP Q) (PDCechNerve.algebraModule A))) := by
  let L := (Functor.whiskeringRight SimplexCategory _ _).obj
    (PDCechNerve.algebraModule A) ⋙ alternatingCofaceMapComplex _
  change QuasiIso (L.map (affineCechAlexanderFrame (P := P) hP Q))
  rw [← comparison_whisker P hP Q, L.map_comp]
  have : QuasiIso (L.map (Functor.whiskerRight j F)) :=
    BigCechVertexFrame.toBig_quasiIso P Q E (fun n => affineBigCechTerm_bounded P Q n hP)
      (affineBigCechTerm_small P hP Q) U
  infer_instance

end SerrePositivity.BhattScholze.Prismatic
