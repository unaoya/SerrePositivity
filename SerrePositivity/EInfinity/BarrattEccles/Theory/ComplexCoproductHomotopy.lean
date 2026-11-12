module

public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-!
# 指定直和の鎖ホモトピー

HA 3.2.4.7 の自由比較で、各二色成分の指定係数射の鎖ホモトピー同値を
全ての arity の直和へ移す。生成元への制限を使い、非有界な複体も扱う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded
variable {A : Type u} [CommRing A] {J : Type v} [Small.{u} J]

/-- 直和包含への制限ごとの指定鎖ホモトピーを、一つの鎖ホモトピーへ束ねる。 -/
def complexCoproductHomotopy (K : J → Complex A) {L : Complex A} (f g : (∐ K) ⟶ L)
    (h : ∀ a, Homotopy (Sigma.ι K a ≫ f) (Sigma.ι K a ≫ g)) : Homotopy f g := by
  let E (i : ℤ) := HomologicalComplex.eval (ModuleCat A) (.up ℤ) i
  let H (i j : ℤ) : (∐ K).X i ⟶ L.X j :=
    (isColimitOfHasCoproductOfPreservesColimit (E i) K).desc
      (Cofan.mk (L.X j) (fun a => (h a).hom i j))
  have hh (a : J) (i j : ℤ) : (Sigma.ι K a).f i ≫ H i j = (h a).hom i j :=
    (isColimitOfHasCoproductOfPreservesColimit (E i) K).fac _ (Discrete.mk a)
  refine { hom := H, zero := ?_, comm := ?_ }
  · intro i j hij
    apply (isColimitOfHasCoproductOfPreservesColimit (E i) K).hom_ext
    intro a
    change (Sigma.ι K a.as).f i ≫ H i j = _
    rw [hh, (h a.as).zero i j hij, comp_zero]
  · intro i
    apply (isColimitOfHasCoproductOfPreservesColimit (E i) K).hom_ext
    intro a
    change (Sigma.ι K a.as).f i ≫ f.f i = (Sigma.ι K a.as).f i ≫
      ((∐ K).d i ((ComplexShape.up ℤ).next i) ≫ H ((ComplexShape.up ℤ).next i) i +
        H i ((ComplexShape.up ℤ).prev i) ≫ L.d ((ComplexShape.up ℤ).prev i) i + g.f i)
    simp only [Preadditive.comp_add, ← Category.assoc]
    rw [(Sigma.ι K a.as).comm]
    simp only [Category.assoc, hh]
    exact (h a.as).comm i

/-- 各成分の指定鎖ホモトピー同値は、指定直和写像の鎖ホモトピー同値になる。 -/
def complexCoproductHomotopyEquiv {K L : J → Complex A}
    (e : ∀ a, HomotopyEquiv (K a) (L a)) : HomotopyEquiv (∐ K) (∐ L) where
  hom := Limits.Sigma.map (fun a => (e a).hom)
  inv := Limits.Sigma.map (fun a => (e a).inv)
  homotopyHomInvId := complexCoproductHomotopy K _ _ (fun a => by
    simpa only [Category.assoc, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_map,
      Category.comp_id, Category.id_comp] using
      (e a).homotopyHomInvId.compRight (Sigma.ι K a))
  homotopyInvHomId := complexCoproductHomotopy L _ _ (fun a => by
    simpa only [Category.assoc, Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_map,
      Category.comp_id, Category.id_comp] using
      (e a).homotopyInvHomId.compRight (Sigma.ι L a))

end SerrePositivity.EInfinity
