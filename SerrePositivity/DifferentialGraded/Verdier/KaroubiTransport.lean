module
public import SerrePositivity.CategoryTheory.KaroubiFullyFaithful

/-! # 圏同値を Karoubi 完備化へ運ぶ

既存の Karoubi 関手延長と retract による本質像判定を使う。
-/
@[expose] public section
noncomputable section
universe u₁ u₂ v₁ v₂
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Idempotents
variable {C : Type u₁} [Category.{v₁} C] {T : Type u₂} [Category.{v₂} T]

lemma karoubiTransport_essSurj (e : C ≌ T) :
    ((functorExtension₂ C T).obj e.functor).EssSurj := by
  refine ⟨fun P => ?_⟩
  let X := e.functor.objPreimage P.X
  exact karoubiExtension_mem_essImage e.functor P X
    ((karoubiRetract P).trans (Retract.ofIso
      ((toKaroubi T).mapIso (e.functor.objObjPreimageIso P.X)).symm))

/-- 同値を既存の Karoubi 関手延長で完備化した同値。 -/
def karoubiEquivalenceTransport (e : C ≌ T) : Karoubi C ≌ Karoubi T := by
  let : ((functorExtension₂ C T).obj e.functor).EssSurj := karoubiTransport_essSurj e
  let : ((functorExtension₂ C T).obj e.functor).IsEquivalence := {}
  exact ((functorExtension₂ C T).obj e.functor).asEquivalence

end SerrePositivity.DifferentialGraded
