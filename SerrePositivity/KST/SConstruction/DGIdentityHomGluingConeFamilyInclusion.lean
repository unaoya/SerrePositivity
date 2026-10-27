module
public import SerrePositivity.KST.SConstruction.DGIdentityHomGluingModuleConeFamily
public import SerrePositivity.KST.SConstruction.DGHomGluingConeConnectingComparison

/-!
概要：元全 Hom を直接保持する cone 族を既存の包含経路へ照合する。
方針：同じ対象と全鎖写像の恒等包含を比較する。
規約：元の実 cone 関手を変更しない。
使われ方：元 gluing の connecting・実逆回転の公開経路との接続。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P : Type w} [DGCategory R P] (F G : DGFunctor R P C)
  (a : ∀ x, ForgetEnrichment.of (Complex R) (F.obj x) ⟶
    ForgetEnrichment.of (Complex R) (G.obj x))
  (h : ∀ x y, F.map x y ≫
      eHomWhiskerLeft (Complex R) (ForgetEnrichment.of (Complex R) (F.obj x)) (a y) =
      G.map x y ≫ eHomWhiskerRight (Complex R) (a x)
        (ForgetEnrichment.of (Complex R) (G.obj y)))
local notation "I" => DGFunctor.id C
local notation "H" => dgIdentityHomGluingFunctor R C F G a h

/-- 概要：同じ元 cone の全加群族は既存の perfect 包含経路に厳密一致する。
方針：元対象・全 Hom 写像の恒等包含だけを簡約する。
規約：全実関手の等号。使われ方：既存の実 connecting と逆回転経路の接続。 -/
lemma dgIdentityHomGluingModuleConeFamily_inclusion :
    dgIdentityHomGluingModuleConeFamily R C F G a h =
      (H).comp (dgHomGluingModuleConeFunctor R C C C (I) (I)) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change ((H).map x y ≫ dgHomGluingConeHomMap R C C C (I) (I) ((H).obj x) ((H).obj y)) ≫
      eqToHom _ =
    (H).map x y ≫ (dgHomGluingConeHomMap R C C C (I) (I) ((H).obj x) ((H).obj y) ≫ 𝟙 _)
  change ((H).map x y ≫ dgHomGluingConeHomMap R C C C (I) (I) ((H).obj x) ((H).obj y)) ≫ 𝟙 _ =
    (H).map x y ≫ dgHomGluingConeHomMap R C C C (I) (I) ((H).obj x) ((H).obj y)
  exact Category.comp_id _
end SerrePositivity.KST.SConstruction
