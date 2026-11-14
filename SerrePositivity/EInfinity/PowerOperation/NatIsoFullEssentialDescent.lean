module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.NatIso

/-!
# 充満・本質的全射な通常関手に沿う同じ自然同型の降下

DAG XIII §2.2 の π/H 比較の全射の自然性に使う。
指定自然同型を、同じ対象の前像とその同型で運ぶ。［一般∞］移動候補。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂ u₃ v₁ v₂ v₃
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

/-- 元の全自然同型を、充満・本質的全射な始域の後へ降ろす。 -/
def natIsoOfFullEssSurj (Q : C ⥤ D) [Q.Full] [Q.EssSurj] (F G : D ⥤ E)
    (e : Q ⋙ F ≅ Q ⋙ G) : F ≅ G :=
  NatIso.ofComponents
    (fun d => (F.mapIso (Q.objObjPreimageIso d)).symm ≪≫
      e.app (Q.objPreimage d) ≪≫ G.mapIso (Q.objObjPreimageIso d))
    (fun {d d'} f => by
      let a := Q.objObjPreimageIso d
      let b := Q.objObjPreimageIso d'
      have h := e.hom.naturality (Q.preimage (a.hom ≫ f ≫ b.inv))
      simp only [Functor.comp_map, Q.map_preimage, Functor.map_comp] at h
      apply (cancel_epi (F.map a.hom)).mp
      apply (cancel_mono (G.map b.inv)).mp
      simpa [a, b, Functor.map_comp, Category.assoc] using h)

end SerrePositivity.EInfinity.PowerOperation
