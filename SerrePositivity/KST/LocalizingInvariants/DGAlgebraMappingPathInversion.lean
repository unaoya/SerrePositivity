module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathProjection
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraMappingPathSurjective

/-!
概要：実 dg 代数では、全射擬同型の反転から全擬同型の反転が従う。
方針：元の mapping-path の全射擬同型な二射影と、厳密な切断式を使う。
規約：任意の値圏を許し、代数や単体集合のモデル構造を入力しない。
使われ方：実 cell 写像模型の標的擬同型不変性を、全射の場合へ帰着する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {C : Type v} [Category.{w} C]

lemma map_isIso_of_inverts_surjective_quasiIso (F : Mon (Complex R) ⥤ C)
    (hF : ∀ {X Y : Mon (Complex R)} (p : X ⟶ Y),
      (∀ n : ℤ, Function.Surjective (p.hom.f n)) → QuasiIso p.hom → IsIso (F.map p))
    {X Y : Mon (Complex R)} (f : X ⟶ Y) (hf : QuasiIso f.hom) : IsIso (F.map f) := by
  let p := MappingPath.projection R f
  let t := MappingPath.target R f
  let e := MappingPath.section_ R f
  have hp : IsIso (F.map p) := hF p (MappingPath.projection_surjective R f)
    (MappingPath.projection_quasiIso R f)
  have ht : IsIso (F.map t) := hF t (MappingPath.target_surjective R f)
    (MappingPath.target_quasiIso R f hf)
  have he : F.map e = inv (F.map p) := by
    apply (cancel_mono (F.map p)).mp
    rw [IsIso.inv_hom_id, ← F.map_comp]
    change F.map (MappingPath.section_ R f ≫ MappingPath.projection R f) = 𝟙 _
    rw [MappingPath.section_projection, F.map_id]
  have hs : IsIso (F.map e) := he ▸ inferInstance
  have hfac : F.map f = F.map e ≫ F.map t := by
    rw [← F.map_comp]
    exact congrArg F.map (MappingPath.section_target R f).symm
  rw [hfac]
  infer_instance

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
