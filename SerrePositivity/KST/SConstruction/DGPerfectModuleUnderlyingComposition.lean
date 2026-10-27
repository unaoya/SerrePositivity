module
public import SerrePositivity.KST.SConstruction.DGPerfectModuleUnderlying

/-!
概要：元 perfect 像の全加群包含と元入力合成の等号を保持する。
方針：元全 Hom 鎖写像の結合則を抽象的な入力で先に証明する。
規約：元対象・元鎖写像を保持する。
使われ方：実逆回転二実像の全評価軸を既定上限のまま回収する。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (E : Type v) [DGCategory R E] [Small.{u} E]
  {C : Type w} [DGCategory R C] {P : Type z} [DGCategory R P]
  (F : DGFunctor R P C) (J : DGFunctor R C (PerfectDGModule R E))

/-- 概要：元入力合成の実加群包含は元全包含との合成に一致。
方針：元全 Hom 鎖写像の結合則と外延性を使う。
規約：元全関手の等号。使われ方：二実像評価の元軸回収。 -/
lemma dgPerfectModuleUnderlying_comp :
    F.comp (dgPerfectModuleUnderlying R E J) =
      dgPerfectModuleUnderlying R E (F.comp J) := by
  apply EnrichedFunctor.ext (Complex R) (fun _ => rfl)
  intro x y
  change F.map x y ≫ (J.map (F.obj x) (F.obj y) ≫ 𝟙 _) =
    (F.map x y ≫ J.map (F.obj x) (F.obj y)) ≫ 𝟙 _
  exact (Category.assoc _ _ _).symm

/-- 概要：元 perfect 像への全包含回収は同じ実加群軸の全回収を与える。
方針：抽象的な元包含の合成則へ元全関手等号を適用する。
規約：実像射を変更しない。使われ方：元実逆回転の二つの全加群軸。 -/
lemma dgPerfectModuleUnderlying_comp_of_eq (G : DGFunctor R P (PerfectDGModule R E))
    (h : F.comp J = G) :
    F.comp (dgPerfectModuleUnderlying R E J) = dgPerfectModuleUnderlying R E G :=
  (dgPerfectModuleUnderlying_comp R E F J).trans
    (congrArg (dgPerfectModuleUnderlying R E) h)
end SerrePositivity.KST.SConstruction
