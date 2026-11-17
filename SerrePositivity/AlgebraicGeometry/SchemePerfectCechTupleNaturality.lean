module

public import SerrePositivity.AlgebraicGeometry.SchemePerfectCechTupleFunctor
public import SerrePositivity.AlgebraicGeometry.SchemeCechTupleBaseChange

/-!
概要：同じ被覆の実際の引き戻しを、二つの nerve の係数関手の自然変換にする。
方針：既存の mapCechNerve の自然性と、同じ refinedPullback の合成則を使う。
規約：全次数で同じ元の被覆の逆像を使う。
使われ方：閉中心への制限を可換な二重 Čech の図式へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
variable {f g : Arrow Scheme.{u}} (F : f ⟶ g) {ι : Type} [DecidableEq ι]
variable (U : ι → g.left.Opens) (p : ℕ) (hp : p.Prime)
variable (hf : ∀ n : SimplexCategoryᵒᵖ, ∀ O, (p : (f.cechNerve.obj n).presheaf.obj O) = 0)
variable (hg : ∀ n : SimplexCategoryᵒᵖ, ∀ O, (p : (g.cechNerve.obj n).presheaf.obj O) = 0)

/-- 同じ被覆の実際の逆像を使う、各項の係数の引き戻し。 -/
def schemePerfectCechTuplePullbackMap (n : SimplexCategory) :
    schemePerfectCechTupleComplex g.hom U p hp hg n ⟶
      schemePerfectCechTupleComplex f.hom (fun i ↦ F.left ⁻¹ᵁ U i) p hp hf n :=
  schemeStructurePerfectCechRefinedPullbackMap ((Arrow.mapCechNerve F).app (op n))
    p hp (hg (op n)) (hf (op n)) (schemeCechTupleOpen g.hom U (op n))
    (schemeCechTupleOpen f.hom (fun i ↦ F.left ⁻¹ᵁ U i) (op n)) id
    (fun t ↦ le_of_eq (schemeCechTupleOpen_mapCechNerve_preimage F U (op n) t))

set_option backward.isDefEq.respectTransparency false in
/-- 実際の引き戻しの各項の写像は、全ての nerve の射に自然。 -/
theorem schemePerfectCechTuplePullback_naturality {m n : SimplexCategory} (a : m ⟶ n) :
    schemePerfectCechTupleMap g.hom U p hp hg a ≫
        schemePerfectCechTuplePullbackMap F U p hp hf hg n =
      schemePerfectCechTuplePullbackMap F U p hp hf hg m ≫
        schemePerfectCechTupleMap f.hom (fun i ↦ F.left ⁻¹ᵁ U i) p hp hf a := by
  let ρ : (Fin (n.len + 1) → ι) → (Fin (m.len + 1) → ι) :=
    fun t j ↦ t (a.toOrderHom j)
  let k := (Arrow.mapCechNerve F).app (op n) ≫ g.cechNerve.map a.op
  have he : f.cechNerve.map a.op ≫ (Arrow.mapCechNerve F).app (op m) = k :=
    (Arrow.mapCechNerve F).naturality a.op
  have hW : ∀ t, schemeCechTupleOpen f.hom (fun i ↦ F.left ⁻¹ᵁ U i) (op n) t ≤
      k ⁻¹ᵁ schemeCechTupleOpen g.hom U (op m) (ρ t) := by
    intro t
    rw [Scheme.Hom.comp_preimage]
    exact (le_of_eq (schemeCechTupleOpen_mapCechNerve_preimage F U (op n) t)).trans
      (((Arrow.mapCechNerve F).app (op n)).preimage_mono
        (schemeCechTupleOpen_map_le g.hom U a.op t))
  have hl := schemeStructurePerfectCechRefinedPullbackMap_compIndex
    (g.cechNerve.map a.op) ((Arrow.mapCechNerve F).app (op n)) k rfl p hp
    (hg (op m)) (hg (op n)) (hf (op n))
    (schemeCechTupleOpen g.hom U (op m)) (schemeCechTupleOpen g.hom U (op n))
    (schemeCechTupleOpen f.hom (fun i ↦ F.left ⁻¹ᵁ U i) (op n)) ρ id
    (schemeCechTupleOpen_map_le g.hom U a.op)
    (fun t ↦ le_of_eq (schemeCechTupleOpen_mapCechNerve_preimage F U (op n) t)) hW
  have hr := schemeStructurePerfectCechRefinedPullbackMap_compIndex
    ((Arrow.mapCechNerve F).app (op m)) (f.cechNerve.map a.op) k he p hp
    (hg (op m)) (hf (op m)) (hf (op n))
    (schemeCechTupleOpen g.hom U (op m)) (schemeCechTupleOpen f.hom (fun i ↦ F.left ⁻¹ᵁ U i) (op m))
    (schemeCechTupleOpen f.hom (fun i ↦ F.left ⁻¹ᵁ U i) (op n)) id ρ
    (fun t ↦ le_of_eq (schemeCechTupleOpen_mapCechNerve_preimage F U (op m) t))
    (schemeCechTupleOpen_map_le f.hom (fun i ↦ F.left ⁻¹ᵁ U i) a.op) hW
  exact hl.trans hr.symm

/-- 同じ被覆の逆像による、実際の Frobenius 係数関手の自然な引き戻し。 -/
def schemePerfectCechTuplePullback :
    schemePerfectCechTupleFunctor g.hom U p hp hg ⟶
      schemePerfectCechTupleFunctor f.hom (fun i ↦ F.left ⁻¹ᵁ U i) p hp hf where
  app := schemePerfectCechTuplePullbackMap F U p hp hf hg
  naturality := fun {m n} a ↦ schemePerfectCechTuplePullback_naturality F U p hp hf hg a

end SerrePositivity.AlgebraicGeometry
